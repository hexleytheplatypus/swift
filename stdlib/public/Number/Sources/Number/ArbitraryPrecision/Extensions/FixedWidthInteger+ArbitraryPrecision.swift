//===--- FixedWidthInteger+ArbitraryPrecision.swift ----------------------===//
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

extension FixedWidthInteger {
    /// Returns the high and low parts of a potentially overflowing addition.
    func addingFullWidth(_ other: Self) -> (high: Self, low: Self) {
        let sum = self.addingReportingOverflow(other)
        return (sum.overflow ? 1 : 0, sum.partialValue)
    }
    
    /// Returns the high and low parts of two seqeuential potentially overflowing additions.
    static func addingFullWidth(_ x: Self, _ y: Self, _ z: Self) -> (high: Self, low: Self) {
        let xy = x.addingReportingOverflow(y)
        let xyz = xy.partialValue.addingReportingOverflow(z)
        let high: Self = (xy.overflow ? 1 : 0) + (xyz.overflow ? 1 : 0)
        return (high, xyz.partialValue)
    }
    
    /// Returns a tuple containing the value that would be borrowed from a higher place and the partial difference of this value and `rhs`.
    func subtractingWithBorrow(_ rhs: Self) -> (borrow: Self, partialValue: Self) {
        let difference = subtractingReportingOverflow(rhs)
        return (difference.overflow ? 1 : 0, difference.partialValue)
    }
    
    /// Returns a tuple containing the value that would be borrowed from a higher place and the partial value of `x` and `y` subtracted from this value.
    func subtractingWithBorrow(_ x: Self, _ y: Self) -> (borrow: Self, partialValue: Self) {
        let firstDifference = subtractingReportingOverflow(x)
        let secondDifference = firstDifference.partialValue.subtractingReportingOverflow(y)
        let borrow: Self = (firstDifference.overflow ? 1 : 0) + (secondDifference.overflow ? 1 : 0)
        return (borrow, secondDifference.partialValue)
    }
}

extension FixedWidthInteger {
    func leftshiftReportingOverflow(_ shift: Self) -> (partialValue: Self, overflow: Self) {
        let lhs = self
        let inverseShift = Self(lhs.bitWidth) - shift
        return (partialValue: lhs << shift, overflow: lhs >> inverseShift)
    }
    
    func rightshiftReportingUnderflow(_ shift: Self) -> (partialValue: Self, underflow: Self) {
        let lhs = self
        let inverseShift = Self(lhs.bitWidth) - shift
        return (partialValue: lhs >> shift, underflow: lhs << inverseShift)
    }
}

extension FixedWidthInteger {
    static func random() -> Self {
        return Self.random(in: Self.min...Self.max)
    }
}
