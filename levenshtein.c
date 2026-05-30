// https://github.com/wooorm/levenshtein.c
// (The MIT License)
// Copyright (c) 2015 Titus Wormer <tituswormer@gmail.com>
// Slightly altered for the proof.
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>

size_t strlen(const char *str) {
  size_t i;
  for (i=0; ; i++)
    if (str[i]==0) return i;
}

// Returns a size_t, depicting the difference between `a` and `b`.
// See <http://en.wikipedia.org/wiki/Levenshtein_distance> for more information.
size_t
levenshtein_n(const char *a, const size_t length, const char *b, const size_t bLength) {
  size_t *cache;
  size_t index = 0;
  size_t bIndex = 0;
  size_t distance;
  size_t bDistance;
  size_t result;
  char code;

  // Shortcut optimizations / degenerate cases.
  if (a == b) {
    return (size_t) 0;
  }

  if (length == 0) {
    return bLength;
  }

  if (bLength == 0) {
    return length;
  }

  cache = calloc(length, sizeof(size_t));

  // initialize the vector.
  while (index < length) {
    cache[index] = index + 1;
    index++;
  }

  // Loop.
  while (bIndex < bLength) {
    code = b[bIndex];
    distance = bIndex;
    result = bIndex;
    bIndex++;
    index = 0;

    while (index < length) {
      if (code == a[index]) {
        bDistance = distance;
      } else {
        bDistance = distance + 1;
      }
      distance = cache[index];

      if (distance > result) {
        if (bDistance > result) {
          result = result + 1;
        } else {
          result = bDistance;
        }
      } else {
        if (bDistance > distance) {
          result = distance + 1;
        } else {
          result = bDistance;
        }
      }

      cache[index] = result;
      index++;
    }
  }

  free(cache);

  return result;
}

size_t
levenshtein(const char *a, const char *b) {
  const size_t length = strlen(a);
  const size_t bLength = strlen(b);

  return levenshtein_n(a, length, b, bLength);
}
