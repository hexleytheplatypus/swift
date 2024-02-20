//===--- ArbitraryPrecisionSignedInteger.swift ------------------------------===//
//
// This source file is part of the Swift.org open source project
//
// Copyright (c) 2014 - 2024 Apple Inc. and the Swift project authors
// Licensed under Apache License v2.0 with Runtime Library Exception
//
// See https://swift.org/LICENSE.txt for license information
// See https://swift.org/CONTRIBUTORS.txt for the list of Swift project authors
//
//===------------------------------------------------------------------------===//

//===--- ArbitraryPrecisionSignedInteger ------------------------------------===//
//===------------------------------------------------------------------------===//

/// A dynamically-sized signed integer.
///
/// The `ArbitraryPrecisionSignedInteger` type uses the system's word-sized `UInt`
/// as its word type, but any word size should work properly.
public struct ArbitraryPrecisionSignedInteger: BinaryInteger {
    internal var _mantissa = ArbitraryPrecisionUnsignedInteger()
    
    /// A Boolean value indicating whether this instance is negative.
    public private(set) var isNegative = false
    
    //===--- Numeric initializers -------------------------------------------===//
    
    /// Creates a new instance equal to zero.
    public init() { }
    
    /// Creates a new instance using `_data` as the data collection.
    init<C: Sequence>(storage: C) where C.Element == UInt {
        defer { self._standardize() }
        self._mantissa = ArbitraryPrecisionUnsignedInteger(storage: storage)
    }
    
    init<N: Sequence>(bits: N) where N.Element: FixedWidthInteger, N.Element: UnsignedInteger {
        self.init(storage: bits.align(to: UInt.self)) /// `_standardize()` called on lower `init`
    }
    
    init<E>(elements: E...) where E: FixedWidthInteger, E: UnsignedInteger {
        self.init(storage: elements.align(to: UInt.self)) /// `_standardize()` called on lower `init`
    }
    
    public init(integerLiteral value: StaticBigInt) {
        defer { self._standardize() }
        self._mantissa = ArbitraryPrecisionUnsignedInteger(integerLiteral: value)
        if value.signum() == -1 { self.isNegative = true }
    }
    
    public init(_ unsignedValue: ArbitraryPrecisionUnsignedInteger, isNegative: Bool = false) {
        defer { self._standardize() }
        self._mantissa = unsignedValue
        self.isNegative = isNegative
    }
    
    public init<T: BinaryInteger>(_ source: T) {
        defer { self._standardize() }
        
        /// Early exit on zero
        if source == T.zero {
            self._mantissa = ArbitraryPrecisionUnsignedInteger()
            return
        }
        
        /// Compute
        var source = source
        if source < 0 as T {
            if source.bitWidth <= UInt64.bitWidth {
                let sourceMag = Int(truncatingIfNeeded: source).magnitude
                self._mantissa = ArbitraryPrecisionUnsignedInteger(sourceMag)
                self.isNegative = true
                return
            } else {
                // Have to kind of assume that we're working with another ArbitraryPrecisionSignedInteger here
                self.isNegative = true
                source *= -1
            }
        }
        
        self._mantissa = ArbitraryPrecisionUnsignedInteger(source)
    }
    
    public init?<T: BinaryInteger>(exactly source: T) {
        self.init(source)
    }
    
    public init<T: BinaryInteger>(truncatingIfNeeded source: T) {
        self.init(source)
    }
    
    public init<T: BinaryInteger>(clamping source: T) {
        self.init(source)
    }
    
    public init<T: BinaryFloatingPoint>(_ source: T) {
        fatalError("FIXME: - Not implemented")
    }
    
    public init?<T: BinaryFloatingPoint>(exactly source: T) {
        fatalError("FIXME: - Not implemented")
    }
    
    //===--- Useful Constants -----------------------------------------------===//
    
    @inlinable public static var zero: Self { Self() }
    @inlinable public static var one: Self { Self(1) }
    @inlinable public static var two: Self { Self(2) }
    @inlinable public static var ten: Self { Self(10) }
    
    //===--- Numeric Classification -----------------------------------------===//
    
    /// A Boolean value indicating whether this instance is equal to zero.
    public var isZero: Bool {
        return _mantissa.isZero
    }
    
    /// A Boolean value indicating whether this instance is non-zero & non-negative.
    public var isNaturalNumber: Bool {
        return isWholeNumber && !isZero
    }
    
    /// A Boolean value indicating whether this instance is non-negative.
    public var isWholeNumber: Bool {
        return !isNegative
    }
    
    /// A Boolean value indicating whether this instance is an Integer.
    /// Note: - ArbitraryPrecisionSignedInteger is always an Integer.
    public let isInteger: Bool = true
    
    /// A Boolean value indicating whether this instance is a Rational number.
    /// Note: - ArbitraryPrecisionSignedInteger is always a Rational number.
    public let isRational: Bool = true
    
    /// A Boolean value indicating whether this instance is a Repeating number.
    /// Note: - ArbitraryPrecisionSignedInteger is never a Repeating number.
    public let isRepeating: Bool = false
    
    /// A Boolean value indicating whether this instance is a Irrational number.
    /// Note: - ArbitraryPrecisionSignedInteger is never an Irrational number.
    public let isIrrational: Bool = false
    
    /// A Boolean value indicating whether this instance is a Real number.
    /// Note: - ArbitraryPrecisionSignedInteger is always a Real number.
    public let isRealNumber: Bool = true
    
    /// A Boolean value indicating whether this instance is a Complex number.
    /// Note: - ArbitraryPrecisionSignedInteger is never a Complex number.
    public let isComplexNumber: Bool = false
    
    //===--- Randomness -----------------------------------------------------===//
    
    //    public static func random() -> Self {
    //        return self.random(in: UInt.min...UInt.max)
    //    }
    
    public static func random(in range: ClosedRange<UInt>) -> Self {
        var x = self.init()
        x._mantissa = ArbitraryPrecisionUnsignedInteger.random(in: range)
        x.isNegative = Bool.random()
        x._standardize()
        return x
    }
    
    //===--- Private Methods ------------------------------------------------===//
    
    /// Standardizes this instance after mutation, making sure zero is nonnegative.
    /// Calling this method satisfies the invariant.
    @_spi(InvariantValidation)
    public mutating func _standardize(source: String = #function) {
        defer { _checkInvariants(source: source + " >> self._standardize()") }
        _mantissa._standardize(source: source)
        
        // Zero is never negative.
        isNegative = isNegative && _mantissa != 0
    }
    
    /// Checks and asserts on invariants -- the invariant must be satisfied
    /// at the end of every mutating method.
    ///
    /// - If `self == 0`, then `isNegative == false`
    @_spi(InvariantValidation)
    public func _checkInvariants(source: String = #function) {
        if _mantissa == 0 {
            assert(isNegative == false, "\(source): isNegative with zero length _storage")
        }
        _mantissa._checkInvariants(source: source)
    }
    
    //===--- Numeric --------------------------------------------------------===//
    
    public typealias Magnitude = ArbitraryPrecisionUnsignedInteger
    public var magnitude: Magnitude {
        return _mantissa
    }
    
    /// Adds `rhs` to this instance, ignoring any signs.
    private mutating func _unsignedAdd(_ rhs: ArbitraryPrecisionSignedInteger) {
        defer { self._standardize() }
        _mantissa += rhs._mantissa
    }
    
    /// Subtracts `rhs` from this instance, ignoring the sign.
    private mutating func _unsignedSubtract(_ rhs: ArbitraryPrecisionSignedInteger) {
        defer { self._standardize() }
        _mantissa -= rhs._mantissa
    }
    
    public func quotientAndRemainder(dividingBy rhs: ArbitraryPrecisionSignedInteger) -> (ArbitraryPrecisionSignedInteger, ArbitraryPrecisionSignedInteger) {
        let (unsQ, unsR) = self._mantissa.quotientAndRemainder(dividingBy: rhs._mantissa)
        
        /// If `numerator` and `denominator` have the same sign, then `quotient` is positive.
        let q = ArbitraryPrecisionSignedInteger(unsQ, isNegative: self.isNegative != rhs.isNegative)
        
        /// Always adopt the `numerator`s sign for the `remainder`
        let r = ArbitraryPrecisionSignedInteger(unsR, isNegative: self.isNegative)
        
        return (q, r)
    }
    
    //===--- Operators ------------------------------------------------------===//
    
    public static func +=(lhs: inout ArbitraryPrecisionSignedInteger, rhs: ArbitraryPrecisionSignedInteger) {
        defer { lhs._standardize() }
        if lhs.isNegative == rhs.isNegative {
            lhs._unsignedAdd(rhs)
        } else {
            lhs -= -rhs
        }
    }
    
    public static func -=(lhs: inout ArbitraryPrecisionSignedInteger, rhs: ArbitraryPrecisionSignedInteger) {
        defer { lhs._standardize() }
        
        // Subtracting something of the opposite sign just adds magnitude.
        guard lhs.isNegative == rhs.isNegative else {
            lhs._unsignedAdd(rhs)
            return
        }
        
        // Compare `lhs` and `rhs` so we can use `_unsignedSubtract` to subtract
        // the smaller magnitude from the larger magnitude.
        switch lhs._compareMagnitude(to: rhs) {
            case .equal:
                lhs = 0
            case .greaterThan:
                lhs._unsignedSubtract(rhs)
            case .lessThan:
                // x - y == -y + x == -(y - x)
                var result = rhs
                result._unsignedSubtract(lhs)
                result.isNegative = !lhs.isNegative
                lhs = result
        }
    }
    
    public static func *=(lhs: inout ArbitraryPrecisionSignedInteger, rhs: ArbitraryPrecisionSignedInteger) {
        defer { lhs._standardize() }
        lhs._mantissa *= rhs._mantissa
        lhs.isNegative = lhs.isNegative != rhs.isNegative
    }
    
    public static func /=(lhs: inout ArbitraryPrecisionSignedInteger, rhs: ArbitraryPrecisionSignedInteger) {
        defer { lhs._standardize() }
        lhs._mantissa /= rhs._mantissa
        lhs.isNegative = lhs.isNegative != rhs.isNegative
    }
    
    public static func %=(lhs: inout ArbitraryPrecisionSignedInteger, rhs: ArbitraryPrecisionSignedInteger) {
        defer { lhs._standardize() }
        lhs._mantissa %= rhs._mantissa
    }
    
    //===--- Operator Shims -------------------------------------------------===//
    
    public static func +(_ lhs: Self, _ rhs: Self) -> Self {
        var lhs = lhs
        lhs += rhs
        return lhs
    }
    
    public static func -(_ lhs: Self, _ rhs: Self) -> Self {
        var lhs = lhs
        lhs -= rhs
        return lhs
    }
    
    public static func *(_ lhs: Self, _ rhs: Self) -> Self {
        var lhs = lhs
        lhs *= rhs
        return lhs
    }
    
    public static func /(_ lhs: Self, _ rhs: Self) -> Self {
        var lhs = lhs
        lhs /= rhs
        return lhs
    }
    
    public static func %(_ lhs: Self, _ rhs: Self) -> Self {
        var lhs = lhs
        lhs %= rhs
        return lhs
    }
    
    //===--- BinaryInteger --------------------------------------------------===//
    
    // take a storage holding _twosComplementData and convert it to positive representation
    private init(convertingPositive _twosComplementData: [UInt]) {
        defer { self._standardize() }
        
        self.isNegative = true
        let storage = ArbitraryPrecisionUnsignedInteger(storage: _twosComplementData)
        let x: ArbitraryPrecisionUnsignedInteger = (~storage) + 1
        self._mantissa = ArbitraryPrecisionUnsignedInteger(storage: x._storage)
        // this is back to representing the negative in a seperate value
    }
    
    /// Returns an array of the value's data using the representation required by `BinaryInteger`.
    /// - This is expressed using two's complement for negative numbers and untouched for positive numbers
    private func _twosComplement() -> [UInt] {
        let data = _mantissa._storage
        
        // Special cases:
        // * Nonnegative values are already in 2's complement
        if isNegative != true { return data }
        
        // * -1 will get zeroed out below, easier to handle here
        if data.count == 1 && data.first == 1 { return [~0] }
        
        let x = ~(_mantissa - 1)
        return x._storage
    }
    
    public var words: [UInt] {
        let twosComplementData = _twosComplement()
        /// Positive numbers align and return as normal
        guard isNegative else { return twosComplementData.align(to: UInt.self) }
        
        var result = twosComplementData.align(to: UInt.self)
        guard let last = result.popLast() else { fatalError("Cannot convert bits to no-bits") }
        guard last.leadingZeroBitCount != 0 else { /// Already proper Two's Complement
            result.append(last)
            return result
        }
        
        /// Correct for proper Two's Complement
        let lastBitWidth = last.leadingZeroBitCount
        var twosComplementCorrection = (UInt.max << (UInt.bitWidth - lastBitWidth))
        twosComplementCorrection |= last
        result.append(twosComplementCorrection)
        return result
    }
    
    /// Returns the minimal number of bits in this value’s binary representation, including the sign bit, and excluding the sign extension.
    public var bitWidth: Int {
        if isZero == true {
            return .zero
        } else {
            let twosComplementData = _twosComplement()
            
            if isNegative == true {
                let inverted = ~(twosComplementData.last!)
                return twosComplementData.count * UInt.bitWidth - (inverted.leadingZeroBitCount - 1)
            }
            
            // If positive, need to make space for at least one zero on high end
            return twosComplementData.count * UInt.bitWidth - (twosComplementData.last!.leadingZeroBitCount + 1)
        }
    }
    
    /// The number of sequential zeros in the least-significant position of this value's binary representation.
    ///
    /// The numbers 1 and zero have zero trailing zeros.
    public var trailingZeroBitCount: Int {
        return _mantissa.trailingZeroBitCount
    }
    
    //===--- Bitwise Operators ----------------------------------------------===//
    
    public static func &=(lhs: inout ArbitraryPrecisionSignedInteger, rhs: ArbitraryPrecisionSignedInteger) {
        defer { lhs._standardize() }
        
        var lhsTemp = ArbitraryPrecisionUnsignedInteger(storage: lhs._twosComplement())
        let rhsTemp = ArbitraryPrecisionUnsignedInteger(storage: rhs._twosComplement())
        
        if lhs.isNegative && rhs.isNegative {
            lhsTemp &= rhsTemp
            lhs = ArbitraryPrecisionSignedInteger(convertingPositive: lhsTemp._storage)
        } else {
            lhs = ArbitraryPrecisionSignedInteger(lhsTemp & rhsTemp)
        }
    }
    
    public static func |=(lhs: inout ArbitraryPrecisionSignedInteger, rhs: ArbitraryPrecisionSignedInteger) {
        defer { lhs._standardize() }
        
        var lhsTemp = ArbitraryPrecisionUnsignedInteger(storage: lhs._twosComplement())
        let rhsTemp = ArbitraryPrecisionUnsignedInteger(storage: rhs._twosComplement())
        
        if lhs.isNegative || rhs.isNegative {
            lhsTemp |= rhsTemp
            lhs = ArbitraryPrecisionSignedInteger(convertingPositive: lhsTemp._storage)
        } else {
            lhs = ArbitraryPrecisionSignedInteger(lhsTemp | rhsTemp)
        }
    }
    
    public static func ^=(lhs: inout ArbitraryPrecisionSignedInteger, rhs: ArbitraryPrecisionSignedInteger) {
        defer { lhs._standardize() }
        
        var lhsTemp = ArbitraryPrecisionUnsignedInteger(storage: lhs._twosComplement())
        let rhsTemp = ArbitraryPrecisionUnsignedInteger(storage: rhs._twosComplement())
        
        if lhs.isNegative != rhs.isNegative {
            lhsTemp ^= rhsTemp
            lhs = ArbitraryPrecisionSignedInteger(convertingPositive: lhsTemp._storage)
        } else {
            lhs = ArbitraryPrecisionSignedInteger(lhsTemp ^ rhsTemp)
        }
    }
    
    public static prefix func ~(x: ArbitraryPrecisionSignedInteger) -> ArbitraryPrecisionSignedInteger {
        return -x - 1
    }
    
    //===--- String methods -------------------------------------------------===//

    /// Creates a new instance from the given string.
    ///
    /// - Parameters:
    ///   - source: The string to parse for the new instance's value. If a
    ///     character in `source` is not in the range `0...9` or `a...z`, case
    ///     insensitive, or is not less than `radix`, the result is `nil`.
    ///   - radix: The radix to use when parsing `source`. `radix` must be in the
    ///     range `2...36`. The default is `10`.
    public init?(_ source: String, radix: Int = 10) {
        assert(2...36 ~= radix, "radix must be in range 2...36")
        var source = source
        
        // Check for a single prefixing hyphen
        let negative = source.hasPrefix("-")
        if negative { source = String(source.dropFirst()) }
        
        guard let storage = ArbitraryPrecisionUnsignedInteger(source, radix: radix) else { return nil }
        
        self._mantissa = storage
        self.isNegative = negative
    }
    
    /// A string representation of this instance's value in base 2.
    public var binaryString: String {
        let result = self.magnitude.binaryString
        if self.isNegative { return "-" + result }
        return result
    }
    
    /// A string representation of this instance's value in base 10.
    public var decimalString: String {
        let result = self.magnitude.decimalString
        if self.isNegative { return "-" + result }
        return result
        
    }
    
    /// A string representation of this instance's value in base 16.
    public var hexString: String {
        let result = self.magnitude.hexString
        if self.isNegative { return "-" + result }
        return result
    }
    
    /// A string representation of this instance's value in base 36.
    public var compactString: String {
        let result = self.magnitude.compactString
        if self.isNegative { return "-" + result }
        return result
    }
    
    //===--- Bit Shift Operators --------------------------------------------===//
    
    public static func <<= <RHS: BinaryInteger>(lhs: inout ArbitraryPrecisionSignedInteger, rhs: RHS) {
        defer { lhs._standardize() }
        
        switch rhs.sign {
            case .negative:
                lhs._mantissa >>= rhs.magnitude
            default:
                lhs._mantissa <<= rhs.magnitude
        }
    }
    
    public static func >>= <RHS: BinaryInteger>(lhs: inout ArbitraryPrecisionSignedInteger, rhs: RHS) {
        defer { lhs._standardize() }
        
        switch rhs.sign {
            case .negative:
                lhs._mantissa <<= rhs.magnitude
            default:
                lhs._mantissa >>= rhs.magnitude
        }
        
        // Handle Special Negative Right-hand Shift Rule
        if lhs.isNegative && lhs._mantissa == 0 {
            lhs._mantissa = .one // But -0 is equivalent to `-1` for two's complement.
        }
    }
}

// MARK: - Codable
extension ArbitraryPrecisionSignedInteger: Codable {
    //===--- Codable --------------------------------------------------------===//
    
    enum CodingKeys: String, CodingKey {
        case bytes
        case negative
    }
    
    public func encode(to encoder: Encoder) throws {
        var container = encoder.container(keyedBy: CodingKeys.self)
        try container.encode(_mantissa, forKey: .bytes)
        try container.encode(isNegative, forKey: .negative)
    }
    
    public init(from decoder: Decoder) throws {
        let values = try decoder.container(keyedBy: CodingKeys.self)
        let mantissa = try values.decode(Magnitude.self, forKey: .bytes)
        let isNegative = try values.decode(Bool.self, forKey: .negative)
        self.init(mantissa, isNegative: isNegative)
    }
}

// MARK: - Comparable
extension ArbitraryPrecisionSignedInteger: Comparable {
    //===--- Comparable -----------------------------------------------------===//
    
    enum _ComparisonResult {
        case lessThan, equal, greaterThan
    }
    
    /// Returns whether this instance is less than, greather than, or equal to the given value.
    private func _compare(to rhs: ArbitraryPrecisionSignedInteger) -> _ComparisonResult {
        // Negative values are less than positive values
        guard isNegative == rhs.isNegative else {
            return isNegative ? .lessThan : .greaterThan
        }
        
        switch _compareMagnitude(to: rhs) {
            case .equal:
                return .equal
            case .lessThan:
                return isNegative ? .greaterThan : .lessThan
            case .greaterThan:
                return isNegative ? .lessThan : .greaterThan
        }
    }
    
    /// Returns whether the magnitude of this instance is less than, greater than, or equal to the magnitude of the given value.
    private func _compareMagnitude(to rhs: ArbitraryPrecisionSignedInteger) -> _ComparisonResult {
        return _mantissa._compareMagnitude(to: rhs._mantissa)
    }
    
    public static func < (lhs: ArbitraryPrecisionSignedInteger, rhs: ArbitraryPrecisionSignedInteger) -> Bool {
        return lhs._compare(to: rhs) == .lessThan
    }
}

// MARK: - CustomDebugStringConvertible
extension ArbitraryPrecisionSignedInteger: CustomDebugStringConvertible {
    //===--- CustomDebugStringConvertible -----------------------------------===//
    
    public var debugDescription: String {
        return "ArbitraryPrecisionSignedInteger(\(hexString), storage: \(_mantissa.debugDescription))"
    }
}

// MARK: - CustomStringConvertible
extension ArbitraryPrecisionSignedInteger: CustomStringConvertible {
    //===--- CustomStringConvertible ----------------------------------------===//
    
    public var description: String {
        return decimalString
    }
}

// MARK: - Equatable
extension ArbitraryPrecisionSignedInteger: Equatable {
    //===--- Equatable ------------------------------------------------------===//
    
    public static func ==(lhs: ArbitraryPrecisionSignedInteger, rhs: ArbitraryPrecisionSignedInteger) -> Bool {
        return lhs._compare(to: rhs) == .equal
    }
}

// MARK: - Hashable
extension ArbitraryPrecisionSignedInteger: Hashable {
    //===--- Hashable -------------------------------------------------------===//
    
    public func hash(into hasher: inout Hasher) {
        hasher.combine(isNegative)
        hasher.combine(_mantissa)
    }
}

// MARK: - Sendable
extension ArbitraryPrecisionSignedInteger: Sendable {
    //===--- Sendable -------------------------------------------------------===//
}

// MARK: - Strideable
extension ArbitraryPrecisionSignedInteger: Strideable {
    //===--- Strideable -----------------------------------------------------===//
}

// MARK: - SignedInteger
extension ArbitraryPrecisionSignedInteger: SignedInteger {
    //===--- SignedInteger --------------------------------------------------===//
}

// MARK: - SignedNumeric
extension ArbitraryPrecisionSignedInteger: SignedNumeric {
    //===--- SignedNumeric --------------------------------------------------===//
    
    public static prefix func -(operand: ArbitraryPrecisionSignedInteger) -> ArbitraryPrecisionSignedInteger {
        var lhs = operand
        lhs.negate()
        return lhs
    }
    
    public mutating func negate() {
        defer { self._standardize() }
        self.isNegative.toggle()
    }
}
