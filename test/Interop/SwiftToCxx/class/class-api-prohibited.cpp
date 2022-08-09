// RUN: %empty-directory(%t)

// RUN: %target-swift-frontend %S/swift-class-in-cxx.swift -typecheck -module-name Class -clang-header-expose-public-decls -emit-clang-header-path %t/class.h

// RUN: not %target-interop-build-clangxx -c %s -I %t -o %t/swift-class-execution.o

#include "class.h"

void test(void * _Nonnull p) {
  // Prohibited to construct class reference directly from opaque pointer.
  Class::ClassWithIntField x(p);
}
