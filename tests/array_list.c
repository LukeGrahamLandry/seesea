// could make assertions a compiler intrinsic, so I don't have to deal with this
// #include "assert.h"

typedef int index_t;
typedef void* value_t;

void* malloc(long size);
void free(void* ptr);
void *memcpy(void* dest, void* src, long n);
int printf(char* format, ...);
// void print_vm_stack_trace();

typedef struct ArrayList {
    value_t* values;
    index_t length;
    index_t capacity;
} ArrayList;

index_t list_set(ArrayList* list, index_t index, value_t value) {
    if (index >= list->length) {
        return -1;
    }
    index_t offset = index * sizeof(value_t);
    *(list->values + offset) = value;
    return 0;
}

void list_resize(ArrayList* list, index_t new_capacity) {
    // assert(new_capacity >= list->length, "Tried to reduce size of list when that would lose elements.");
    value_t* old_values = list->values;
    if (new_capacity < 1) {
        free(old_values);
        list->values = 0;
        list->capacity = 0;
    } else {
        list->values = malloc(sizeof(value_t) * new_capacity);
        if (list->capacity > 0) {
            memcpy(list->values, old_values, sizeof(value_t) * list->length);
            free(old_values);
        }
        list->capacity = new_capacity;
    }
    return;
}

ArrayList* list_create(index_t capacity) {
    ArrayList* list = malloc(sizeof(ArrayList));
    list->length = 0;
    list_resize(list, capacity);
    // print_vm_stack_trace();
    return list;
}

// Since this may resize the list, any pointers into it are invalidated after calling it.
void list_push(ArrayList* list, value_t value) {
    if (list->length >= list->capacity) {
        list_resize(list, list->capacity * 2);
    }
    index_t offset = list->length * sizeof(value_t);
    value_t* end = list->values + offset;
    *end = value;
    list->length = list->length + 1;
    return;
}

value_t list_get(ArrayList* list, index_t index) {
    if (index >= list->length) {
        return 0;
    }
    index_t offset = index * sizeof(value_t);
    return *(list->values + offset);
}

value_t list_remove(ArrayList* list, index_t index) {
    if (index >= list->length) {
        return 0;
    }
    index_t offset = index * sizeof(value_t);
    // TODO
    return 0;
}

value_t list_pop(ArrayList* list) {
    return list_remove(list, list->length - 1);
}

void list_free(ArrayList* list) {
    if (list->capacity >= 1) {
        free(list->values);
    }
    free(list);
    return;
}

index_t test() {
    index_t a = 4;
    index_t b = 5;
    index_t c = 6;
    ArrayList* list = list_create(5);
    list_push(list, (value_t) &a);
    list_push(list, (value_t) &b);
    list_push(list, (value_t) &c);
    index_t* bb_addr = (index_t*) list_get(list, 1);
    index_t bb = *bb_addr;
    list_free(list);
    if (bb < c) {
        return 0;
    } else {
        return -1;
    }
}
