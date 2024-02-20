//===--- BinaryInteger+Sign.swift -----------------------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2024 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===----------------------------------------------------------------------===//

/// FIXME: - Resolve Sign-based usage
enum Sign {
    case positive
    case none
    case negative
}

extension BinaryInteger {
    var sign: Sign {
        switch self.signum() {
            case 0:  return Sign.none
            case 1:  return Sign.positive
            default: return Sign.negative
        }
    }
}

