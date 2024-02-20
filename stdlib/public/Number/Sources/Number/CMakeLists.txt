#===--- CMakeLists.txt - Number support library --------------------------===#
#
# This source file is part of the Swift.org open source project
#
# Copyright (c) 2024 Apple Inc. and the Swift project authors
# Licensed under Apache License v2.0 with Runtime Library Exception
#
# See https://swift.org/LICENSE.txt for license information
# See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
#
#===----------------------------------------------------------------------===#

list(APPEND swift_runtime_library_compile_flags -I${SWIFT_SOURCE_DIR}/stdlib/include -I${SWIFT_SOURCE_DIR}/include)

add_swift_target_library(swiftNumber ${SWIFT_STDLIB_LIBRARY_BUILD_TYPES} IS_STDLIB
  Number.swift
  ArbitraryPrecision/Extensions/Array+Group.swift
  ArbitraryPrecision/Extensions/BinaryInteger+Sign.swift
  ArbitraryPrecision/Extensions/BinaryIntegerAlignment.swift
  ArbitraryPrecision/Extensions/FixedWidthInteger+ArbitraryPrecision.swift
  ArbitraryPrecision/Extensions/StaticBigInt+Extensions.swift
  ArbitraryPrecision/ArbitraryPrecisionUnsignedInteger.swift
  ArbitraryPrecision/ArbitraryPrecisionSignedInteger.swift

  SWIFT_COMPILE_FLAGS
    ${SWIFT_STANDARD_LIBRARY_SWIFT_FLAGS}

  C_COMPILE_FLAGS
    ${swift_runtime_library_compile_flags}

  INSTALL_IN_COMPONENT stdlib

  MACCATALYST_BUILD_FLAVOR "zippered"
)
