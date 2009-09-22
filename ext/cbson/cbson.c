/*
 * Copyright 2009 10gen, Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * This file contains C implementations of some of the functions needed by the
 * bson module. If possible, these implementations should be used to speed up
 * BSON encoding and decoding.
 */

#include "ruby.h"


#if HAVE_RUBY_ST_H
#include "ruby/st.h"
#endif
#if HAVE_ST_H
#include "st.h"
#endif

#if HAVE_RUBY_REGEX_H
#include "ruby/regex.h"
#endif
#if HAVE_REGEX_H
#include "regex.h"
#endif

#include <assert.h>
#include <math.h>


#define INITIAL_BUFFER_SIZE 256

static VALUE Binary;
static VALUE Undefined;
static VALUE Time;
static VALUE ObjectID;
static VALUE DBRef;
static VALUE Code;
static VALUE RegexpOfHolding;
static VALUE OrderedHash;

// this sucks. but for some reason these moved around between 1.8 and 1.9
#ifdef ONIGURUMA_H
#define IGNORECASE ONIG_OPTION_IGNORECASE
#define MULTILINE ONIG_OPTION_MULTILINE
#define EXTENDED ONIG_OPTION_EXTEND
#else
#define IGNORECASE RE_OPTION_IGNORECASE
#define MULTILINE RE_OPTION_MULTILINE
#define EXTENDED RE_OPTION_EXTENDED
#endif

/* TODO we ought to check that the malloc or asprintf was successful
 * and raise an exception if not. */
#ifdef _MSC_VER
#define INT2STRING(buffer, i)                   \
    {                                           \
        int vslength = _scprintf("%d", i) + 1;  \
        *buffer = malloc(vslength);             \
        _snprintf(*buffer, vslength, "%d", i);  \
    }
#elif defined(__MINGW32__)
#define INT2STRING(buffer, i)                   \
    {                                           \
        int vslength = log10(i) + 2;  \
        *buffer = malloc(vslength);             \
        _snprintf(*buffer, vslength, "%d", i);  \
    }
#else
#define INT2STRING(buffer, i) asprintf(buffer, "%d", i);
#endif

// this sucks too.
#ifndef RREGEXP_SRC_PTR
#define RREGEXP_SRC_PTR(r) RREGEXP(r)->str
#define RREGEXP_SRC_LEN(r) RREGEXP(r)->len
#endif

typedef struct {
    char* buffer;
    int size;
    int position;
} bson_buffer;

static char zero = 0;
static char one = 1;

static int cmp_char(const void* a, const void* b) {
    return *(char*)a - *(char*)b;
}

static void write_doc(bson_buffer* buffer, VALUE hash, VALUE check_keys);
static int write_element(VALUE key, VALUE value, VALUE extra);
static VALUE elements_to_hash(const char* buffer, int max);

static bson_buffer* buffer_new(void) {
    bson_buffer* buffer;
    buffer = ALLOC(bson_buffer);
    assert(buffer);

    buffer->size = INITIAL_BUFFER_SIZE;
    buffer->position = 0;
    buffer->buffer = ALLOC_N(char, INITIAL_BUFFER_SIZE);
    assert(buffer->buffer);

    return buffer;
}

static void buffer_free(bson_buffer* buffer) {
    assert(buffer);
    assert(buffer->buffer);

    free(buffer->buffer);
    free(buffer);
}

static void buffer_resize(bson_buffer* buffer, int min_length) {
    int size = buffer->size;
    if (size >= min_length) {
        return;
    }
    while (size < min_length) {
        size *= 2;
    }
    buffer->buffer = REALLOC_N(buffer->buffer, char, size);
    assert(buffer->buffer);
    buffer->size = size;
}

static void buffer_assure_space(bson_buffer* buffer, int size) {
    if (buffer->position + size <= buffer->size) {
        return;
    }
    buffer_resize(buffer, buffer->position + size);
}

/* returns offset for writing */
static int buffer_save_bytes(bson_buffer* buffer, int size) {
    int position = buffer->position;
    buffer_assure_space(buffer, size);
    buffer->position += size;
    return position;
}

static void buffer_write_bytes(bson_buffer* buffer, const char* bytes, int size) {
    buffer_assure_space(buffer, size);

    memcpy(buffer->buffer + buffer->position, bytes, size);
    buffer->position += size;
}

static VALUE pack_extra(bson_buffer* buffer, VALUE check_keys) {
    return rb_ary_new3(2, INT2NUM((int)buffer), check_keys);
}

static void write_name_and_type(bson_buffer* buffer, VALUE name, char type) {
    buffer_write_bytes(buffer, &type, 1);
    buffer_write_bytes(buffer, RSTRING_PTR(name), RSTRING_LEN(name));
    buffer_write_bytes(buffer, &zero, 1);
}

static int write_element_allow_id(VALUE key, VALUE value, VALUE extra, int allow_id) {
    bson_buffer* buffer = (bson_buffer*)NUM2INT(rb_ary_entry(extra, 0));
    VALUE check_keys = rb_ary_entry(extra, 1);

    if (TYPE(key) == T_SYMBOL) {
        // TODO better way to do this... ?
        key = rb_str_new2(rb_id2name(SYM2ID(key)));
    }

    if (TYPE(key) != T_STRING) {
        rb_raise(rb_eTypeError, "keys must be strings or symbols");
    }

    if (!allow_id && strcmp("_id", RSTRING_PTR(key)) == 0) {
        return ST_CONTINUE;
    }

    if (check_keys == Qtrue) {
        int i;
        if (RSTRING_LEN(key) > 0 && RSTRING_PTR(key)[0] == '$') {
            rb_raise(rb_eRuntimeError, "key must not start with '$'");
        }
        for (i = 0; i < RSTRING_LEN(key); i++) {
            if (RSTRING_PTR(key)[i] == '.') {
                rb_raise(rb_eRuntimeError, "key must not contain '.'");
            }
        }
    }

    switch(TYPE(value)) {
    case T_BIGNUM:
        {
            VALUE as_f;
            int int_value;
            if (rb_funcall(value, rb_intern(">"), 1, INT2NUM(2147483647)) == Qtrue ||
                rb_funcall(value, rb_intern("<"), 1, INT2NUM(-2147483648)) == Qtrue) {
                rb_raise(rb_eRangeError, "MongoDB can only handle 4-byte ints"
                         " - try converting to a double before saving");
            }
            write_name_and_type(buffer, key, 0x10);
            as_f = rb_funcall(value, rb_intern("to_f"), 0);
            int_value = NUM2LL(as_f);
            buffer_write_bytes(buffer, (char*)&int_value, 4);
            break;
        }
    case T_FIXNUM:
        {
            int int_value = FIX2INT(value);
            write_name_and_type(buffer, key, 0x10);
            buffer_write_bytes(buffer, (char*)&int_value, 4);
            break;
        }
    case T_TRUE:
        {
            write_name_and_type(buffer, key, 0x08);
            buffer_write_bytes(buffer, &one, 1);
            break;
        }
    case T_FALSE:
        {
            write_name_and_type(buffer, key, 0x08);
            buffer_write_bytes(buffer, &zero, 1);
            break;
        }
    case T_FLOAT:
        {
            double d = NUM2DBL(value);
            write_name_and_type(buffer, key, 0x01);
            buffer_write_bytes(buffer, (char*)&d, 8);
            break;
        }
    case T_NIL:
        {
            write_name_and_type(buffer, key, 0x0A);
            break;
        }
    case T_HASH:
        {
            write_name_and_type(buffer, key, 0x03);
            write_doc(buffer, value, check_keys);
            break;
        }
    case T_ARRAY:
        {
            int start_position, length_location, items, i, obj_length;
            VALUE* values;

            write_name_and_type(buffer, key, 0x04);
            start_position = buffer->position;

            // save space for length
            length_location = buffer_save_bytes(buffer, 4);

            items = RARRAY_LEN(value);
            values = RARRAY_PTR(value);
            for(i = 0; i < items; i++) {
                char* name;
                VALUE key;
                INT2STRING(&name, i);
                key = rb_str_new2(name);
                write_element(key, values[i], pack_extra(buffer, check_keys));
                free(name);
            }

            // write null byte and fill in length
            buffer_write_bytes(buffer, &zero, 1);
            obj_length = buffer->position - start_position;
            memcpy(buffer->buffer + length_location, &obj_length, 4);
            break;
        }
    case T_STRING:
        {
            if (strcmp(rb_class2name(RBASIC(value)->klass),
                       "XGen::Mongo::Driver::Code") == 0) {
                int start_position, length_location, length, total_length;
                write_name_and_type(buffer, key, 0x0F);

                start_position = buffer->position;
                length_location = buffer_save_bytes(buffer, 4);

                length = RSTRING_LEN(value) + 1;
                buffer_write_bytes(buffer, (char*)&length, 4);
                buffer_write_bytes(buffer, RSTRING_PTR(value), length - 1);
                buffer_write_bytes(buffer, &zero, 1);
                write_doc(buffer, rb_funcall(value, rb_intern("scope"), 0), Qfalse);

                total_length = buffer->position - start_position;
                memcpy(buffer->buffer + length_location, &total_length, 4);

                break;
            } else {
                int length = RSTRING_LEN(value) + 1;
                write_name_and_type(buffer, key, 0x02);
                buffer_write_bytes(buffer, (char*)&length, 4);
                buffer_write_bytes(buffer, RSTRING_PTR(value), length - 1);
                buffer_write_bytes(buffer, &zero, 1);
                break;
            }
        }
    case T_SYMBOL:
        {
            const char* str_value = rb_id2name(SYM2ID(value));
            int length = strlen(str_value) + 1;
            write_name_and_type(buffer, key, 0x0E);
            buffer_write_bytes(buffer, (char*)&length, 4);
            buffer_write_bytes(buffer, str_value, length);
            break;
        }
    case T_OBJECT:
        {
            // TODO there has to be a better way to do these checks...
            const char* cls = rb_class2name(RBASIC(value)->klass);
            if (strcmp(cls, "XGen::Mongo::Driver::Binary") == 0 ||
                strcmp(cls, "ByteBuffer") == 0) {
                const char subtype = strcmp(cls, "ByteBuffer") ?
                    (const char)FIX2INT(rb_funcall(value, rb_intern("subtype"), 0)) : 2;
                VALUE string_data = rb_funcall(value, rb_intern("to_s"), 0);
                int length = RSTRING_LEN(string_data);
                write_name_and_type(buffer, key, 0x05);
                if (subtype == 2) {
                    const int other_length = length + 4;
                    buffer_write_bytes(buffer, (const char*)&other_length, 4);
                    buffer_write_bytes(buffer, &subtype, 1);
                }
                buffer_write_bytes(buffer, (const char*)&length, 4);
                if (subtype != 2) {
                    buffer_write_bytes(buffer, &subtype, 1);
                }
                buffer_write_bytes(buffer, RSTRING_PTR(string_data), length);
                break;
            }
            if (strcmp(cls, "XGen::Mongo::Driver::ObjectID") == 0) {
                VALUE as_array = rb_funcall(value, rb_intern("to_a%