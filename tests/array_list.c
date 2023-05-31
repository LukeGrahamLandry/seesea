// could make assertions a compiler intrinsic, so I don't have to deal with this
// #include "assert.h"

void* malloc(long size);
void free(void* ptr);
void *memcpy(void* dest, void* src, long n);

typedef struct ArrayList {
    void** values;
    int length;
    int capacity;
} ArrayList;

int list_set(ArrayList* list, int index, void* value) {
    if (index >= list->length) {
        return -1;
    }
    int offset = index * sizeof(void*);
    *(list->values + offset) = value;
    return 0;
}

void list_resize(ArrayList* list, int new_capacity) {
    // assert(new_capacity >= list->length, "Tried to reduce size of list when that would lose elements.");
    void** old_values = list->values;
    list->values = malloc(sizeof(void*) * new_capacity);
    list->capacity = new_capacity;
    memcpy(list->values, old_values, sizeof(void*) * list->length);
    free(old_values);
    return;
}

ArrayList list_create(int capacity) {
    ArrayList list;
    list.length = 0;
    list_resize(&list, capacity);
    return list;
}

// Since this may resize the list, any pointers into it are invalidated after calling it.
void list_push(ArrayList* list, void* value) {
    if (list->length >= list->capacity) {
        list_resize(list, list->capacity * 2);
    }
    *(list->values + list->length) = value;
    list->length = list->length + 1;
    return;
}

void* list_get(ArrayList* list, int index) {
    if (index >= list->length) {
        return 0;
    }
    int offset = index * sizeof(void*);
    return *(list->values + offset);
}

void* list_remove(ArrayList* list, int index) {
    if (index >= list->length) {
        return 0;
    }
    int offset = index * sizeof(void*);
    // TODO
    return 0;
}

void* list_pop(ArrayList* list) {
    return list_remove(list, list->length - 1);
}

void list_clear(ArrayList* list) {
    free(list->values);
    list->length = 0;
    list->capacity = 0;
    return;
}
