//===--- ArbitraryPrecisionUnsignedInteger.swift ----------------------------===//
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

//===--- ArbitraryPrecisionUnsignedInteger ----------------------------------===//
//===------------------------------------------------------------------------===//

/// A dynamically-sized unsigned integer.
///
/// The `ArbitraryPrecisionUnsignedInteger` type uses the system's word-sized
/// `UInt` as its word type, but any word size should work properly.
public struct ArbitraryPrecisionUnsignedInteger: BinaryInteger {

    /// The binary representation of the value's magnitude, with the least significant word at index `0`. (Trailing-to-Leading or little-endian order)
    ///
    /// - `_storage` has no trailing zero elements
    /// - If `self == 0`, then `_storage == []`
    internal var _storage: [UInt] = []

    //===--- Numeric initializers -------------------------------------------===//

    /// Creates a new instance equal to zero.
    public init() { } /// `_standardize()` call unnecessary

    /// Creates a new instance using `_data` as the data collection.
    init<C: Sequence>(storage: C) where C.Element == UInt {
        defer { self._standardize() }
        self._storage = Array(storage)
    }

    init<N: Sequence>(bits: N) where N.Element: FixedWidthInteger, N.Element: UnsignedInteger {
        self.init(storage: bits.align(to: UInt.self))     /// `_standardize()` called by `init<C: Sequence>(storage: C)`
    }

    init<E>(elements: E...) where E: FixedWidthInteger, E: UnsignedInteger {
        self.init(storage: elements.align(to: UInt.self)) /// `_standardize()` called by `init<C: Sequence>(storage: C)`
    }

    public init(integerLiteral value: StaticBigInt) {
        self.init(storage: value.align(to: UInt.self))    /// `_standardize()` called by `init<C: Sequence>(storage: C)`
    }

    public init<T: BinaryInteger>(_ source: T) {
        guard source != T.zero else { self.init(); return }
        self.init(storage: [source].align(to: UInt.self)) /// `_standardize()` called by `init<C: Sequence>(storage: C)`
    }

    public init?<T: BinaryInteger>(exactly source: T) {
        self.init(source) /// `_standardize()` called by `init<C: Sequence>(storage: C)`
    }

    public init<T: BinaryInteger>(truncatingIfNeeded source: T) {
        self.init(source) /// `_standardize()` called by `init<C: Sequence>(storage: C)`
    }

    public init<T: BinaryInteger>(clamping source: T) {
        self.init(source) /// `_standardize()` called by `init<C: Sequence>(storage: C)`
    }

    public init<T: BinaryFloatingPoint>(_ source: T) {
        fatalError("FIXME: - Not implemented")
    }

    public init?<T: BinaryFloatingPoint>(exactly source: T) {
        fatalError("FIXME: - Not implemented")
    }

    //===--- Useful Constants -----------------------------------------------===//

    public static var zero: Self { return Self() }
    public static var one: Self { return Self(1) }
    public static var two: Self { return Self(2) }
    public static var ten: Self { return Self(10) }

    //===--- Numeric Classification -----------------------------------------===//

    /// A Boolean value indicating whether this instance is equal to zero.
    public var isZero: Bool {
        return _storage.isEmpty
    }

    /// A Boolean value indicating whether this instance is non-zero.
    public var isNaturalNumber: Bool {
        return !isZero
    }

    /// A Boolean value indicating whether this instance is a Whole number.
    /// - Note: ArbitraryPrecisionUnsignedInteger is always a Whole number.
    public let isWholeNumber: Bool = true

    /// A Boolean value indicating whether this instance is an Integer.
    /// Note: - ArbitraryPrecisionUnsignedInteger is always an Integer.
    public let isInteger: Bool = true

    /// A Boolean value indicating whether this instance is a Rational number.
    /// Note: - ArbitraryPrecisionUnsignedInteger is always a Rational number.
    public let isRational: Bool = true

    /// A Boolean value indicating whether this instance is a Repeating number.
    /// Note: - ArbitraryPrecisionUnsignedInteger is never a Repeating number.
    public let isRepeating: Bool = false

    /// A Boolean value indicating whether this instance is an Irrational number.
    /// Note: - ArbitraryPrecisionUnsignedInteger is never an Irrational number.
    public let isIrrational: Bool = false

    /// A Boolean value indicating whether this instance is a Real number.
    /// Note: - ArbitraryPrecisionUnsignedInteger is always a Real number.
    public let isRealNumber: Bool = true

    /// A Boolean value indicating whether this instance is a Complex number.
    /// Note: - ArbitraryPrecisionUnsignedInteger is never a Complex number.
    public let isComplexNumber: Bool = false

    //===--- Randomness -----------------------------------------------------===//

    //    public static func random() -> Self {
    //        return self.random(in: UInt.min...UInt.max)
    //    }

    public static func random(in range: ClosedRange<UInt>) -> Self {
        var _data: [UInt] = []
        for _ in 0..<UInt.random(in: range) {
            _data.append(UInt.random())
        }
        return self.init(storage: _data)
    }

    //===--- Private Access -------------------------------------------------===//

    private var count: Int {
        return _storage.count
    }

    private subscript(_ index: Int) -> UInt {
        get {
            if index <= (self.count - 1) { return self._storage[index] }
            return UInt.zero
        }
        set {
            if index > (self.count - 1) {
                let increment = index - (self.count - 1)
                for _ in 0..<increment {
                    self._storage.append(.zero)
                }
            }

            self._storage[index] = newValue
        }
    }

    //===--- Private Methods ------------------------------------------------===//

    /// Standardizes this instance after mutation, removing trailing zeros.
    /// Calling this method satisfies the invariant.
    @_spi(InvariantValidation)
    public mutating func _standardize(source: String = #function) {
        defer { _checkInvariants(source: source + " >> _standardize()") }
        while _storage.last == .zero {
            _storage.removeLast()
        }
    }

    /// Checks and asserts on invariants -- the invariant must be satisfied
    /// at the end of every mutating method.
    ///
    /// - `_storage` has no trailing zero elements
    @_spi(InvariantValidation)
    public func _checkInvariants(source: String = #function) {
        assert(_storage.last != .zero, "\(source): extra zeroes in _storage")
    }

    //===--- Numeric --------------------------------------------------------===//

    /// Adds `rhs` to this instance, ignoring any signs.
    private mutating func _unsignedAdd(_ rhs: ArbitraryPrecisionUnsignedInteger) {
        defer { self._standardize() }

        let commonCount = Swift.min(self.count, rhs.count)
        let maxCount = Swift.max(self.count, rhs.count)
        _storage.reserveCapacity(maxCount)

        // Add the words up to the common count, carrying any overflows
        var carry: UInt = .zero
        for i in 0..<commonCount {
            (carry, _storage[i]) = UInt.addingFullWidth(_storage[i], rhs._storage[i], carry)
        }

        // If there are leftover words in `self`, just need to handle any carries
        if self.count > rhs.count {
            for i in commonCount..<maxCount {
                // No more action needed if there's nothing to carry
                if carry == .zero { break }
                (carry, _storage[i]) = _storage[i].addingFullWidth(carry)
            }

            // If there are leftover words in `rhs`, need to copy to `self` with carries
        } else if self.count < rhs.count {
            for i in commonCount..<maxCount {
                // Append remaining words if nothing to carry
                if carry == .zero {
                    _storage.append(contentsOf: rhs._storage.suffix(from: i))
                    break
                }
                let sum: UInt
                (carry, sum) = rhs._storage[i].addingFullWidth(carry)
                _storage.append(sum)
            }
        }

        // If there's any carry left, add it now
        if carry != .zero {
            _storage.append(1)
        }
    }

    /// Subtracts `rhs` from this instance, ignoring the sign.
    ///
    /// - Precondition: `rhs.magnitude <= self.magnitude` (unchecked, done in public `-=(lhs:_)`)
    /// - Precondition: `rhs.count <= self.count`
    private mutating func _unsignedSubtract(_ rhs: ArbitraryPrecisionUnsignedInteger) {
        defer { self._standardize() }
        assert(rhs.count <= self.count)

        var carry: UInt = .zero
        for i in 0..<rhs.count {
            (carry, _storage[i]) = _storage[i].subtractingWithBorrow(rhs._storage[i], carry)
        }

        for i in rhs.count..<self.count {
            // No more action needed if there's nothing to carry
            if carry == .zero { break }
            (carry, _storage[i]) = _storage[i].subtractingWithBorrow(carry)
        }
        assert(carry == .zero)
    }

    /// Multiplies this instance with `rhs`, ignoring any signs.
    private mutating func _unsignedMultiply(_ rhs: ArbitraryPrecisionUnsignedInteger) {
        defer { self._standardize() }

        // If either `lhs` or `rhs` is zero, the result is zero.
        guard !self.isZero && !rhs.isZero else {
            self = .zero
            return
        }

        var newData: [UInt] = Array(repeating: .zero, count: self.count + rhs.count)
        let (a, b) = self.count > rhs.count ? (self._storage, rhs._storage) : (rhs._storage, self._storage)
        assert(a.count >= b.count)

        var carry: UInt = .zero
        for ai in 0..<a.count {
            carry = .zero
            for bi in 0..<b.count {
                // Each iteration needs to perform this operation:
                //
                //     newData[ai + bi] += (a[ai] * b[bi]) + carry
                //
                // However, `a[ai] * b[bi]` produces a double-width result, and both
                // additions can overflow to a higher word. The following two lines
                // capture the low word of the multiplication and additions in
                // `newData[ai + bi]` and any addition overflow in `carry`.
                let product = a[ai].multipliedFullWidth(by: b[bi])
                (carry, newData[ai + bi]) = UInt.addingFullWidth(newData[ai + bi], product.low, carry)

                // Now we combine the high word of the multiplication with any addition
                // overflow. It is safe to add `product.high` and `carry` here without
                // checking for overflow, because if `product.high == .max - 1`, then
                // `carry <= 1`. Otherwise, `carry <= 2`.
                //
                // Worst-case (aka 9 + 9*9 + 9):
                //
                //       newData         a[ai]        b[bi]         carry
                //      0b11111111 + (0b11111111 * 0b11111111) + 0b11111111
                //      0b11111111 + (0b11111110_____00000001) + 0b11111111
                //                   (0b11111111_____00000000) + 0b11111111
                //                   (0b11111111_____11111111)
                //
                // Second-worse case:
                //
                //      0b11111111 + (0b11111111 * 0b11111110) + 0b11111111
                //      0b11111111 + (0b11111101_____00000010) + 0b11111111
                //                   (0b11111110_____00000001) + 0b11111111
                //                   (0b11111111_____00000000)
                assert(!product.high.addingReportingOverflow(carry).overflow)
                carry = product.high &+ carry
            }

            // Leftover `carry` is inserted in new highest word.
            assert(newData[ai + b.count] == .zero)
            newData[ai + b.count] = carry
        }

        _storage = newData
    }

    /// Divides this instance by `rhs`, ignoring any signs and returning the `remainder`.
    ///
    /// - Precondition: `!rhs.isZero`
    /// - Returns: The `remainder` of this value divided by `rhs`.
    @discardableResult
    private mutating func _unsignedDivide(_ rhs: ArbitraryPrecisionUnsignedInteger) -> ArbitraryPrecisionUnsignedInteger {
        precondition(!rhs.isZero, "Divided by zero")
        defer { self._standardize() }

        // Handle quick cases that don't require division:
        // If `abs(self) < abs(rhs)`, the result is zero, remainder = self
        // If `abs(self) == abs(rhs)`, the result is 1, remainder = 0
        switch _compareMagnitude(to: rhs) {
            case .lessThan:
                defer { self._storage = [] } /// `_standardize()` call unnecessary when directly setting `_storage` to `[]` (this is equivalent to `self = .zero`), but will happen because of `defer` blocks.
                return self
            case .equal:
                self = .one
                return .zero
            default:
                break
        }

        var tempSelf = self.magnitude
        let n = tempSelf.bitWidth - rhs.magnitude.bitWidth
        var quotient: ArbitraryPrecisionUnsignedInteger = .zero
        var tempRHS = rhs.magnitude << n
        var tempQuotient: ArbitraryPrecisionUnsignedInteger = 1 << n

        for _ in (0...n).reversed() {
            if tempRHS._compareMagnitude(to: tempSelf) != .greaterThan {
                tempSelf -= tempRHS
                quotient += tempQuotient
            }
            tempRHS >>= 1
            tempQuotient >>= 1
        }

        // `tempSelf` is the remainder - match sign of original `self`
        tempSelf._standardize()

        self = quotient
        return tempSelf
    }

    /// Returns the quotient and remainder of this value divided by the given value.
    ///
    /// - Parameter rhs: The value to divide this value by.
    /// - Returns: A tuple containing the `quotient` and `remainder` of this value divided by `rhs`.
    public func quotientAndRemainder(dividingBy rhs: ArbitraryPrecisionUnsignedInteger) -> (quotient: ArbitraryPrecisionUnsignedInteger, remainder: ArbitraryPrecisionUnsignedInteger) {
        var x = self
        let r = x._unsignedDivide(rhs) /// `_standardize()` called by `_unsignedDivide(:_)`
        return (x, r)
    }

    //===--- Operators ------------------------------------------------------===//

    public static func +=(lhs: inout ArbitraryPrecisionUnsignedInteger, rhs: ArbitraryPrecisionUnsignedInteger) {
        lhs._unsignedAdd(rhs) /// `_standardize()` called by `_unsignedAdd(:_)`
    }

    public static func -=(lhs: inout ArbitraryPrecisionUnsignedInteger, rhs: ArbitraryPrecisionUnsignedInteger) {
        // Compare `lhs` and `rhs` so we can use `_unsignedSubtract` to subtract the smaller magnitude from the larger magnitude.
        switch lhs._compareMagnitude(to: rhs) {
            case .equal:
                lhs._storage = [] /// `_standardize()` call unnecessary when directly setting `_storage` to `[]` (this is equivalent to `lhs = .zero`)
            case .greaterThan:
                lhs._unsignedSubtract(rhs) /// `_standardize()` called by `_unsignedSubtract(:_)`
            case .lessThan:
                /// Because `x - y == -y + x == -(y - x)`, this type is `Unsigned` it will return `2` instead of `-2` for `2 - 4`
                var result = rhs
                result._unsignedSubtract(lhs) /// `_standardize()` called by `_unsignedSubtract(:_)`
                lhs = result
        }
    }

    public static func *=(lhs: inout ArbitraryPrecisionUnsignedInteger, rhs: ArbitraryPrecisionUnsignedInteger) {
        lhs._unsignedMultiply(rhs) /// `_standardize()` called by `_unsignedMultiply(:_)`
    }

    public static func /=(lhs: inout ArbitraryPrecisionUnsignedInteger, rhs: ArbitraryPrecisionUnsignedInteger) {
        precondition(!rhs.isZero, "Division by zero in quotient operation")
        lhs = lhs.quotientAndRemainder(dividingBy: rhs).quotient /// `_standardize()` called by `quotientAndRemainder(:_)`
    }

    public static func %=(lhs: inout ArbitraryPrecisionUnsignedInteger, rhs: ArbitraryPrecisionUnsignedInteger) {
        precondition(!rhs.isZero, "Division by zero in remainder operation")
        lhs = lhs.quotientAndRemainder(dividingBy: rhs).remainder /// `_standardize()` called by `quotientAndRemainder(:_)`
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

    /// A collection containing the words of this value's binary
    /// representation, in order from the least significant to most significant.
    public var words: [UInt] {
        return _storage.align(to: UInt.self)
    }

    /// The number of bits used for storage of this value. Always a multiple of `UInt.bitWidth`.
    public var bitWidth: Int {
        if isZero == true { return .zero }
        return _storage.count * UInt.bitWidth - _storage.last!.leadingZeroBitCount + 1
    }

    /// The number of sequential zeros in the least-significant position of this
    /// value's binary representation.
    ///
    /// The numbers 1 and zero have zero trailing zeros.
    public var trailingZeroBitCount: Int {
        guard !isZero == true else { return .zero }

        let i = _storage.firstIndex(where: { $0 != .zero })!
        assert(_storage[i] != .zero)
        return i * UInt.bitWidth + _storage[i].trailingZeroBitCount
    }

    //===--- Bitwise Operators ----------------------------------------------===//

    public static func &=(lhs: inout ArbitraryPrecisionUnsignedInteger, rhs: ArbitraryPrecisionUnsignedInteger) {
        defer { lhs._standardize() }
        guard !lhs.isZero, !rhs.isZero else {
            lhs = .zero /// if either is `.zero`, `&` is always `.zero`
            return
        }

        /// Perform bitwise `&` on words that both `lhs` and `rhs` have.
        for i in 0..<Swift.max(lhs.count, rhs.count) {
            lhs[i] &= rhs[i]
        }
    }

    public static func |=(lhs: inout ArbitraryPrecisionUnsignedInteger, rhs: ArbitraryPrecisionUnsignedInteger) {
        defer { lhs._standardize() }

        /// Perform bitwise `|` on words that both `lhs` and `rhs` have.
        for i in 0..<Swift.max(lhs.count, rhs.count) {
            lhs[i] |= rhs[i]
        }
    }

    public static func ^=(lhs: inout ArbitraryPrecisionUnsignedInteger, rhs: ArbitraryPrecisionUnsignedInteger) {
        defer { lhs._standardize() }

        /// Perform bitwise `^` on words that both `lhs` and `rhs` have.
        for i in 0..<Swift.max(lhs.count, rhs.count) {
            lhs[i] ^= rhs[i]
        }
    }

    public static prefix func ~(x: ArbitraryPrecisionUnsignedInteger) -> ArbitraryPrecisionUnsignedInteger {
        return ArbitraryPrecisionUnsignedInteger(storage: x._storage.map { ~$0 }) /// `_standardize()` called by `init<C: Sequence>(storage: C)`
    }

    //===--- Other arithmetic -----------------------------------------------===//
    /// Returns the greatest common divisor for this value and `other`.
    public func greatestCommonDivisor(with other: Self) -> Self {
        // Quick return if either is zero
        if other.isZero {
            return magnitude
        }
        if isZero == true {
            return other.magnitude
        }

        var (x, y) = (self.magnitude, other.magnitude)
        let (xLSB, yLSB) = (x.trailingZeroBitCount, y.trailingZeroBitCount)

        // Remove any common factor of two
        let commonPower = Swift.min(xLSB, yLSB)
        x >>= commonPower
        y >>= commonPower

        // Remove any remaining factor of two
        if xLSB != commonPower {
            x >>= xLSB - commonPower
        }
        if yLSB != commonPower {
            y >>= yLSB - commonPower
        }

        while !x.isZero {
            // Swap values to ensure that `x >= y`.
            if x._compareMagnitude(to: y) == .lessThan {
                swap(&x, &y)
            }

            // Subtract smaller and remove any factors of two
            x._unsignedSubtract(y)
            x >>= x.trailingZeroBitCount
        }

        // Add original common factor of two back into result
        y <<= commonPower
        return y
    }

    public static func greatestCommonDivisor(_ lhs: Self, _ rhs: Self) -> Self {
        return lhs.greatestCommonDivisor(with: rhs)
    }

    /// Returns the least common multiple for this value and `other`.
    public func leastCommonMultiple(with other: Self) -> Self {
        let gcd = greatestCommonDivisor(with: other)
        if _compareMagnitude(to: other) == .lessThan {
            return ((self / gcd) * other).magnitude
        } else {
            return ((other / gcd) * self).magnitude
        }
    }

    public static func leastCommonMultiple(_ lhs: Self, _ rhs: Self) -> Self {
        return lhs.leastCommonMultiple(with: rhs)
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
        let radix = UInt(radix)

        func valueForCodeUnit(_ unit: Unicode.UTF16.CodeUnit) -> UInt? {
            switch unit {
                    // "0"..."9"
                case 48...57: return UInt(unit - 48)
                    // "a"..."z"
                case 97...122: return UInt(unit - 87)
                    // "A"..."Z"
                case 65...90: return UInt(unit - 55)
                    // invalid character
                default: return nil
            }
        }

        // Remove Underscores
        source.removeAll(where: { $0 == "_" })

        // Loop through characters, multiplying
        for value in source.utf16.map(valueForCodeUnit) {
            // Character must be valid and less than radix
            guard let value = value else { return nil }
            guard value < radix else { return nil }

            self *= Self(radix)
            self += Self(value)
        }
    }

    /// A string representation of this instance's value in base 2.
    public var binaryString: String {
        return String(self, radix: 2)
    }

    /// A string representation of this instance's value in base 10.
    public var decimalString: String {
        return String(self, radix: 10)
    }

    /// A string representation of this instance's value in base 16.
    public var hexString: String {
        return String(self, radix: 16, uppercase: true)
    }

    /// A string representation of this instance's value in base 36.
    public var compactString: String {
        return String(self, radix: 36, uppercase: true)
    }

    //===--- Bit Shift Operators --------------------------------------------===//

    public static func <<= <RHS: BinaryInteger>(lhs: inout ArbitraryPrecisionUnsignedInteger, rhs: RHS) {
        defer { lhs._standardize() }
        guard !lhs.isZero else { return }
        guard rhs != .zero else { return }
        guard rhs > .zero else {
            lhs >>= .zero - rhs
            return
        }

        var rhs = rhs
        var prepends: [UInt] = []
        let wordWidth = RHS(UInt.bitWidth)

        /// While `rhs` is greater than `UInt.bitWidth`, we'll remove as many `UInt.bitWidth` as we can.
        while (rhs >= wordWidth) {
            prepends.append(.zero)
            rhs -= wordWidth
        }

        if !prepends.isEmpty {
            lhs._storage = prepends + lhs._storage
        }

        guard rhs != .zero else { return } // Exit early if `rhs` is a multiple of `UInt.bitWidth`

        var partialValue: UInt = .zero
        for index in 0...lhs.count {
            let (partial, overflow) = lhs[index].leftshiftReportingOverflow(UInt(rhs))
            partialValue |= partial // `or` should work here, because our values should never overlap the same bits
            lhs[index] = partialValue
            partialValue = overflow
        }
    }

    public static func >>= <RHS: BinaryInteger>(lhs: inout ArbitraryPrecisionUnsignedInteger, rhs: RHS) {
        defer { lhs._standardize() }
        guard !lhs.isZero else { return }
        guard rhs != .zero else { return }
        guard rhs > .zero else {
            lhs <<= .zero - rhs
            return
        }

        var rhs = rhs
        let wordWidth = RHS(UInt.bitWidth)

        /// While `rhs` is greater than `UInt.bitWidth`, we'll remove as many `UInt.bitWidth` as we can.
        while (rhs >= wordWidth) {
            lhs._storage = Array(lhs._storage.dropFirst())
            rhs -= wordWidth
        }

        // Exit early if `lhs` has already had all of it's `_storage` elements removed (NOTE: `isZero` checks `_storage.isEmpty`)
        guard !lhs.isZero else { return }
        guard rhs != .zero else { return } // Exit early if `rhs` is a multiple of `UInt.bitWidth`

        var partialValue: UInt = .zero
        for index in (0..<lhs.count).reversed() {
            let (partial, underflow) = lhs[index].rightshiftReportingUnderflow(UInt(rhs))
            partialValue |= partial // `or` should work here, because our values should never overlap the same bits
            lhs[index] = partialValue
            partialValue = underflow
        }
    }
}

// MARK: - Codable
extension ArbitraryPrecisionUnsignedInteger: Codable {
    //===--- Codable --------------------------------------------------------===//

    enum CodingKeys: String, CodingKey {
        case bytes
    }

    public func encode(to encoder: Encoder) throws {
        var container = encoder.container(keyedBy: CodingKeys.self)
        try container.encode(_storage.align(to: UInt8.self), forKey: .bytes)
    }

    public init(from decoder: Decoder) throws {
        let values = try decoder.container(keyedBy: CodingKeys.self)
        let bytes = try values.decode(Array<UInt8>.self, forKey: .bytes)
        self.init(storage: bytes.align(to: UInt.self))
    }
}

// MARK: - Comparable
extension ArbitraryPrecisionUnsignedInteger: Comparable {
    //===--- Comparable -----------------------------------------------------===//

    /// Returns whether the magnitude of this instance is less than, greater than, or equal to the magnitude of the given value.
    internal func _compareMagnitude(to rhs: Self) -> ArbitraryPrecisionSignedInteger._ComparisonResult {
        guard self.count == rhs.count else {
            return self.count < rhs.count ? .lessThan : .greaterThan
        }

        // Equal number of words: compare from most significant word
        for i in (0..<self.count).reversed() {
            if _storage[i] < rhs._storage[i] { return .lessThan }
            if _storage[i] > rhs._storage[i] { return .greaterThan }
        }
        return .equal
    }

    public static func < (lhs: Self, rhs: Self) -> Bool {
        return lhs._compareMagnitude(to: rhs) == .lessThan
    }
}

// MARK: - CustomDebugStringConvertible
extension ArbitraryPrecisionUnsignedInteger: CustomDebugStringConvertible {
    //===--- CustomDebugStringConvertible -----------------------------------===//

    public var debugDescription: String {
        return "ArbitraryPrecisionUnsignedInteger(\(hexString), words: \(self.count))"
    }
}

// MARK: - CustomStringConvertible
extension ArbitraryPrecisionUnsignedInteger: CustomStringConvertible {
    //===--- CustomStringConvertible ----------------------------------------===//

    public var description: String {
        return decimalString
    }
}

// MARK: - Equatable
extension ArbitraryPrecisionUnsignedInteger: Equatable {
    //===--- Equatable ------------------------------------------------------===//

    public static func ==(lhs: Self, rhs: Self) -> Bool {
        return lhs._compareMagnitude(to: rhs) == .equal
    }
}

// MARK: - Exponentiation
extension ArbitraryPrecisionUnsignedInteger {
    //===--- Exponentiation -------------------------------------------------===//

    func exponent(_ exponent: Self) -> Self {
        if exponent == .zero {
            return .one
        } else if exponent % .two == .zero {
            let halfResult = self.exponent(exponent / .two)
            return halfResult * halfResult
        } else {
            let halfResult = self.exponent((exponent - .one) / .two)
            return self * halfResult * halfResult
        }
    }
}

//// MARK: - Factorial
//extension ArbitraryPrecisionUnsignedInteger {
//    public func factorial() -> Self {
//        return FactorialGenerator.of(self)
//    }
//}

// MARK: - Hashable
extension ArbitraryPrecisionUnsignedInteger: Hashable {
    //===--- Hashable -------------------------------------------------------===//

    public func hash(into hasher: inout Hasher) {
        hasher.combine(_storage)
    }
}

// MARK: - Sendable
extension ArbitraryPrecisionUnsignedInteger: Sendable {
    //===--- Sendable -------------------------------------------------------===//
}

// MARK: - Strideable
extension ArbitraryPrecisionUnsignedInteger: Strideable {
    //===--- Strideable -----------------------------------------------------===//
}

// MARK: - UnsignedInteger
extension ArbitraryPrecisionUnsignedInteger: UnsignedInteger {
    //===--- UnsignedInteger ------------------------------------------------===//
}

// MARK: - Primality
extension ArbitraryPrecisionUnsignedInteger {
    //===--- Primality ------------------------------------------------------===//

    public var isPrime: Bool {
        if self.isEven { /// Handle even numbers
            if self == .two { return true }
            return false
        }

        if self <= 3 { /// Handle small odd numbers
            if self <= .one {
                return false
            }
            if self <= 3 {
                return true
            }
        }

        if self.isMultiple(of: 3) {
            return false
        }

        var i: Self = 5
        while i * i <= self {
            if self.isMultiple(of: i) {
                return false
            }

            if self.isMultiple(of: (i + .two)) {
                return false
            }

            i += 6
        }
        return true
    }

    public var primeFactors: Array<Self> {
        var copy = self
        var factors: [Self] = []
        for divisor in .two ..< copy {
            while copy % divisor == .zero {
                factors.append(divisor)
                copy /= divisor
            }
        }
        return factors
    }

    /// Helpers
    private var isOdd: Bool {
        guard !self.isZero else { return false }
        return self._storage[0] & 1 == 1
    }

    private var isEven: Bool {
        return !self.isOdd
    }
}

