//===--- BinaryIntegerAlignment.swift -------------------------------------===//
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

extension Sequence where Element: BinaryInteger {
    func align<Output>(to cast: Output.Type) -> [Output] where Output: FixedWidthInteger, Output: UnsignedInteger {
        var result: [Output] = []
        for each in self { result.append(contentsOf: each.words.align(to: cast)) }
        return result
    }
}

extension Sequence where Element: FixedWidthInteger, Element: UnsignedInteger {
    func align<Output>(to cast: Output.Type) -> [Output] where Output: FixedWidthInteger, Output: UnsignedInteger {
        typealias Input = Element
        let inputs: [Input] = Array(self)
        
        let (inputQuotient, inputRemainder) = Input.bitWidth.quotientAndRemainder(dividingBy: 8)
        let (outputQuotient, outputRemainder) = Output.bitWidth.quotientAndRemainder(dividingBy: 8)
        guard (inputRemainder == 0), (outputRemainder == 0) else { fatalError("bitWidth not byte compatible") }
        
        var result: [Output] = []
        
        if Input.bitWidth == Output.bitWidth {
            /// Passthru
            for input in inputs { result.append(Output(input)) }
        } else if Input.bitWidth > Output.bitWidth {
            precondition((inputQuotient % outputQuotient) == 0, "bitWidths with remainders are not handled")
            
            /// Slice `Input` down to `Output`
            var ratio: Int!
            let (quotient, remainder) = Input.bitWidth.quotientAndRemainder(dividingBy: Output.bitWidth)
            if remainder == 0 {
                ratio = quotient
            } else {
                ratio = quotient + 1
            }
            
            for var value in inputs {
                for _ in 0..<ratio {
                    result.append(Output(truncatingIfNeeded: value))
                    value >>= Output.bitWidth
                }
            }
        } else if Input.bitWidth < Output.bitWidth {
            precondition((outputQuotient % inputQuotient) == 0, "bitWidths with remainders are not handled")
            
            /// Combine `Input` up to `Output`
            let ratio = (Output.bitWidth / Input.bitWidth)
            let chunks = inputs.groups(of: ratio)
            
            for chunk in chunks {
                var output = Output.zero
                for (index, value) in chunk.enumerated() {
                    let shifted = Output(truncatingIfNeeded: value) << (index * (Output.bitWidth / ratio))
                    output |= shifted
                }
                result.append(output)
            }
        }
        
        return result
    }
}
