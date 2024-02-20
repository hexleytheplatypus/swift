//===--- StaticBigInt+Extensions.swift ------------------------------------===//
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

public extension StaticBigInt {
    func words() -> [UInt] {
        var chunkCount: Int!
        if UInt.bitWidth >= self.bitWidth {
            chunkCount = 1
        } else {
            let (quotient, remainder) = self.bitWidth.quotientAndRemainder(dividingBy: UInt.bitWidth)
            if remainder == 0 {
                chunkCount = quotient
            } else {
                chunkCount = quotient + 1
            }
        }
        
        var result: [UInt] = []
        for index in 0..<chunkCount {
            result.append(self[index])
        }
        
        /// Handle conversion of `Two's Complement` back to a positive-only
        if self.signum() == -1 {
            let temp = ArbitraryPrecisionUnsignedInteger(storage: result.map({ ~$0 }))
            result = (temp + .one)._storage
        }
        
        return result
    }
    
    func align<Output>(to cast: Output.Type) -> [Output] where Output: FixedWidthInteger, Output: UnsignedInteger {
        return self.words().align(to: cast)
    }
}
