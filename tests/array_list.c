// could make assertions a compiler intrinsic, so I don't have to deal with this
// #include "assert.h"

void* malloc(long size);
void free(void* ptr);

struct ArrayList {
    void** values;
    int length;
    int capacity;
};

int list_set(struct ArrayList* list, int index, void* value) {
    if (index >= list->length) {
        return -1;
    }
    *(list->values + index) = value;
    return 0;
}

void list_resize(struct ArrayList* list, int new_capacity) {
    // assert(new_capacity >= list->length, "Tried to reduce size of list when that would lose elements.");
    void** old_values = list->values;
    list->values = malloc(sizeof(void*) * new_capacity);
    list->capacity = new_capacity;
    // TODO: memcpy
    for (int i=0;i<list->length;i++){
        void* value = *(old_values + i);
        list_set(list, i, value);
    }
    free(old_values);
}

struct ArrayList list_create(int capacity) {
    struct ArrayList list;
    list.length = 0;
    list_resize(&list, capacity);
    return list;
}

// Since this may resize the list, any pointers into it are invalidated after calling it.
void list_push(struct ArrayList* list, void* value) {
    if (list->length >= list->capacity) {
        list_resize(list, list->capacity * 2);
    }
    *(list->values + list->length) = value;
    list->length++;
}

void* list_get(struct ArrayList* list, int index) {
    if (index >= list->length) {
        return 0;
    }
    return *(list->values + index);
}

void* list_remove(struct ArrayList* list, int index) {
    if (index >= list->length) {
        return 0;
    }
    // TODO
}

void* list_pop(struct ArrayList* list) {
    list_remove(list, list->length - 1);
}

// This frees the memory of the list.
void list_clear(struct ArrayList* list) {
    free(list->values);
    list->length = 0;
    list->capacity = 0;
}
