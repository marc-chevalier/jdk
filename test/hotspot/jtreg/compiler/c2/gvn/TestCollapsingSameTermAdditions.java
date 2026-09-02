/*
 * Copyright (c) 2025 Red Hat and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package compiler.c2.gvn;

import compiler.lib.generators.Generators;
import compiler.lib.generators.RestrictableGenerator;
import compiler.lib.ir_framework.Test;
import compiler.lib.ir_framework.*;
import static compiler.lib.ir_framework.IRNode.*;
import jdk.test.lib.Asserts;


/*
 * @test
 * @bug 8325495 8347555 8374495
 * @summary C2 should optimize addition of the same terms by collapsing them into one multiplication.
 * @library /test/lib /
 * @run driver ${test.main.class}
 */
public class TestCollapsingSameTermAdditions {
    private static final RestrictableGenerator<Integer> GEN_INT = Generators.G.ints();
    private static final RestrictableGenerator<Long> GEN_LONG = Generators.G.longs();

    public static void main(String[] args) {
        TestFramework.run();
    }

    @Run(test = {
            "addTo2",
            "addTo3",
            "addTo4",
            "shiftAndAddTo4",
            "mulAndAddTo4",
            "addTo5",
            "addTo6",
            "addTo7",
            "addTo8",
            "addTo16",
            "addAndShiftTo16",
            "addTo42",
            "addAandBTo42",
            "addATo42_BTo41",
            "mulAndAddTo42",
            "mulAndAddToMax",
            "mulAndAddToOverflow",
            "mulAndAddToZero",
            "mulAndAddToMinus1",
            "mulAndAddToMinus42",
            "rightPrecedence",
            "rightPrecedenceShift",
            "complexShiftPattern",
            "nestedAddPattern",
            "complexPrecedence",
            "simplifyToParam",
            "simplifyToConst",
            "complexShiftPatternAddNotSimplified",
            "complexShiftPatternAddNotSimplified2",
            "complexShiftPatternSubNotSimplified",
            "complexShiftPatternSubNotSimplified2",
            "complexShiftPatternSubNotSimplified3",
            "differenceOfConsecutivePowersOfTwo",
            "differenceOfConsecutivePowersOfTwoWithNoise",
            "differenceOfAlmostConsecutivePowersOfTwo",
            "addingTwiceTheSamePowerOfTwo",
            "addingTooManyPowersOfTwo",
            "overflowInt1",
            "overflowInt2",
            "overflowInt3",
            "overflowInt4",
            "overflowInt5",
            "overflowInt6",
            "overflowInt7",
            "sumInProduct",
            "complicated",
    })
    private void runIntTests() {
        for (int a : new int[] { 0, 1, Integer.MIN_VALUE, Integer.MAX_VALUE, GEN_INT.next() }) {
            Asserts.assertEQ(a * 2, addTo2(a));
            Asserts.assertEQ(a * 3, addTo3(a));
            Asserts.assertEQ(a * 4, addTo4(a));
            Asserts.assertEQ(a * 4, shiftAndAddTo4(a));
            Asserts.assertEQ(a * 4, mulAndAddTo4(a));
            Asserts.assertEQ(a * 5, addTo5(a));
            Asserts.assertEQ(a * 6, addTo6(a));
            Asserts.assertEQ(a * 7, addTo7(a));
            Asserts.assertEQ(a * 8, addTo8(a));
            Asserts.assertEQ(a * 16, addTo16(a));
            Asserts.assertEQ(a * 16, addAndShiftTo16(a));
            Asserts.assertEQ(a * 42, addTo42(a));
            Asserts.assertEQ(a * 42, mulAndAddTo42(a));
            Asserts.assertEQ(a * Integer.MAX_VALUE, mulAndAddToMax(a));
            Asserts.assertEQ(a * Integer.MIN_VALUE, mulAndAddToOverflow(a));
            Asserts.assertEQ(0, mulAndAddToZero(a));
            Asserts.assertEQ(a * -1, mulAndAddToMinus1(a));
            Asserts.assertEQ(a * -42, mulAndAddToMinus42(a));
            Asserts.assertEQ(a * 3, rightPrecedence(a));
            Asserts.assertEQ(a * 4, rightPrecedenceShift(a));
            Asserts.assertEQ(a * 7, complexShiftPattern(a));
            Asserts.assertEQ(a * 4, nestedAddPattern(a));
            Asserts.assertEQ(a * 6, complexShiftPatternAddNotSimplified(a));
            Asserts.assertEQ(a * 33, complexShiftPatternAddNotSimplified2(a));
            Asserts.assertEQ(a * 60, complexShiftPatternSubNotSimplified(a));
            Asserts.assertEQ(a * 31, complexShiftPatternSubNotSimplified2(a));
            Asserts.assertEQ(a * 60, complexShiftPatternSubNotSimplified3(a));
            Asserts.assertEQ((a << 5) - (a << 4), differenceOfConsecutivePowersOfTwo(a));
            Asserts.assertEQ((a << 6) - (a << 4), differenceOfAlmostConsecutivePowersOfTwo(a));
            Asserts.assertEQ((a << 4) + (a << 4), addingTwiceTheSamePowerOfTwo(a));
            Asserts.assertEQ((a << 6) + (a << 4) + (a << 2), addingTooManyPowersOfTwo(a));
            Asserts.assertEQ(a * 0x7f_ff_ff_fe + (a << 1), overflowInt1(a));
            Asserts.assertEQ(a * 0x7f_ff_ff_fe + (a << 1) - a * 0x80_00_00_00, overflowInt2(a));
            Asserts.assertEQ(a << 33, overflowInt3(a));
            Asserts.assertEQ(a << 33, overflowInt4(a));
            Asserts.assertEQ(((a << 16) << 15) + (a << 31), overflowInt5(a));
            Asserts.assertEQ(((a << 16) << 15) + (a << 31), overflowInt6(a));
            Asserts.assertEQ(0, overflowInt7(a));

            for (int b : new int[] { 0, 1, Integer.MIN_VALUE, Integer.MAX_VALUE, GEN_INT.next() }) {
                Asserts.assertEQ(a * 42 + b * 42, addAandBTo42(a, b));
                Asserts.assertEQ(a * 42 + b * 41, addATo42_BTo41(a, b));
                Asserts.assertEQ(((a << 5) - b) - (a << 4) + b, differenceOfConsecutivePowersOfTwoWithNoise(a, b));
                Asserts.assertEQ(((a + b) << 10) + (a - (b << 1)) * 1_024, sumInProduct(a, b));

                for (int c : new int[] { 0, 1, Integer.MIN_VALUE, Integer.MAX_VALUE, GEN_INT.next() }) {
                    Asserts.assertEQ(b, simplifyToParam(a, b, c));
                    Asserts.assertEQ(0, simplifyToConst(a, b, c));
                    Asserts.assertEQ(b + c - 42, complicated(a, b, c, a, b, c));
                    Asserts.assertEQ(c + a - 42, complicated(a, b, c, b, c, a));
                    Asserts.assertEQ(a + b - 42, complicated(a, b, c, c, a, b));
                    Asserts.assertEQ((b - 2) + (a + 3) - 42, complicated(a, b, c, c + 1, b - 2, a + 3));
                    Asserts.assertEQ((b + 2) + (c - 3) - 42, complicated(a, b, c, a - 1, b + 2, c - 3));
                }
            }
        }
    }

    @Run(test = {
            "mulAndAddToIntOverflowL",
            "mulAndAddToMaxL",
            "mulAndAddToOverflowL",
            "rightPrecedenceL",
            "rightPrecedenceShiftL",
            "complexShiftPatternL",
            "nestedAddPatternL",
            "complexPrecedenceL",
    })
    private void runLongTests() {
        for (long a : new long[] { 0, 1, Long.MIN_VALUE, Long.MAX_VALUE, GEN_LONG.next() }) {
            Asserts.assertEQ(a * (Integer.MAX_VALUE + 1L), mulAndAddToIntOverflowL(a));
            Asserts.assertEQ(a * Long.MAX_VALUE, mulAndAddToMaxL(a));
            Asserts.assertEQ(a * Long.MIN_VALUE, mulAndAddToOverflowL(a));
            Asserts.assertEQ(a * 3L, rightPrecedenceL(a));
            Asserts.assertEQ(a * 4L, rightPrecedenceShiftL(a));
            Asserts.assertEQ(a * 7L, complexShiftPatternL(a));
            Asserts.assertEQ(a * 4L, nestedAddPatternL(a));
            Asserts.assertEQ(a * 5L, complexPrecedenceL(a));
        }
    }

    @Run(test = {
            "bitShiftToOverflow",
            "bitShiftToOverflowL"
    })
    private void runBitShiftTests() {
        Asserts.assertEQ(95, bitShiftToOverflow());
        Asserts.assertEQ(191L, bitShiftToOverflowL());
    }

    // ----- integer tests -----
    @Test
    @IR(counts = { ADD_I, "1" })
    @IR(failOn = LSHIFT_I)
    private static int addTo2(int a) {
        return a + a; // Simple additions like a + a should be kept as-is
    }

    @Test
    @IR(counts = { ADD_I, "1", LSHIFT_I, "1" })
    private static int addTo3(int a) {
        return a + a + a; // a*3 => (a<<1) + a
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { LSHIFT_I, "1" })
    private static int addTo4(int a) {
        return a + a + a + a; // a*4 => a<<2
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { LSHIFT_I, "1" })
    private static int shiftAndAddTo4(int a) {
        return (a << 1) + a + a; // a*2 + a + a => a*3 + a => a*4 => a<<2
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { LSHIFT_I, "1" })
    private static int mulAndAddTo4(int a) {
        return a * 3 + a; // a*4 => a<<2
    }

    @Test
    @IR(counts = { ADD_I, "1", LSHIFT_I, "1" })
    private static int addTo5(int a) {
        return a + a + a + a + a; // a*5 => (a<<2) + a
    }

    @Test
    @IR(counts = { ADD_I, "1", LSHIFT_I, "2" })
    private static int addTo6(int a) {
        return a + a + a + a + a + a; // a*6 => (a<<1) + (a<<2)
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { LSHIFT_I, "1", SUB_I, "1" })
    private static int addTo7(int a) {
        return a + a + a + a + a + a + a; // a*7 => (a<<3) - a
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { LSHIFT_I, "1" })
    private static int addTo8(int a) {
        return a + a + a + a + a + a + a + a; // a*8 => a<<3
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { LSHIFT_I, "1" })
    private static int addTo16(int a) {
        return a + a + a + a + a + a + a + a + a + a
                + a + a + a + a + a + a; // a*16 => a<<4
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { LSHIFT_I, "1" })
    private static int addAndShiftTo16(int a) {
        return (a + a) << 3; // a<<(3 + 1) => a<<4
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { MUL_I, "1" })
    private static int addTo42(int a) {
        return a + a + a + a + a + a + a + a + a + a
                + a + a + a + a + a + a + a + a + a + a
                + a + a + a + a + a + a + a + a + a + a
                + a + a + a + a + a + a + a + a + a + a
                + a + a; // a*42
    }

    @Test
    @IR(counts = { ADD_I, "1", MUL_I, "1" })
    private static int  addAandBTo42(int a, int b) {
        return a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b
                + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b
                + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b
                + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b
                + a + b + a + b; // == a*42 + b*42 => 42 * (a + b)
    }

    @Test
    @IR(counts = { ADD_I, "1", MUL_I, "2" })
    private static int addATo42_BTo41(int a, int b) {
        return a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b
                + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b
                + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b
                + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b + a + b
                + a + b + a; // == a*42 + b*41
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { MUL_I, "1" })
    private static int mulAndAddTo42(int a) {
        return a * 40 + a + a; // a*41 + a => a*42
    }

    private static final int INT_MAX_MINUS_ONE = Integer.MAX_VALUE - 1;

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { LSHIFT_I, "1", SUB_I, "1" })
    private static int mulAndAddToMax(int a) {
        return a * INT_MAX_MINUS_ONE + a; // = a * (MAX - 1) + a = a * MAX = a * (MIN - 1) = a * MIN - a => a << 63 - a
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { LSHIFT_I, "1" })
    private static int mulAndAddToOverflow(int a) {
        return a * Integer.MAX_VALUE + a; // a*(MAX+1) => a*(MIN) => a<<31
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { CON_I, "1" })
    private static int mulAndAddToZero(int a) {
        return a * -1 + a; // 0
    }

    @Test
    @IR(failOn = { ADD_I, LSHIFT_I })
    @IR(counts = { SUB_I, "1" })
    private static int mulAndAddToMinus1(int a) {
        return a * -2 + a; // = -a => 0 - a
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { MUL_I, "1" })
    private static int mulAndAddToMinus42(int a) {
        return a * -43 + a; // a*-42
    }

    // --- long tests ---
    @Test
    @IR(failOn = ADD_L)
    @IR(counts = { LSHIFT_L, "1" })
    private static long mulAndAddToIntOverflowL(long a) {
        return a * Integer.MAX_VALUE + a; // a*(INT_MAX+1)
    }

    private static final long LONG_MAX_MINUS_ONE = Long.MAX_VALUE - 1;

    @Test
    @IR(failOn = ADD_L)
    @IR(counts = { LSHIFT_L, "1", SUB_L, "1" })
    private static long mulAndAddToMaxL(long a) {
        return a * LONG_MAX_MINUS_ONE + a; // a*MAX = a*(MIN-1) = a*MIN - 1 => (a<<63) - 1
    }

    @Test
    @IR(failOn = ADD_L)
    @IR(counts = { LSHIFT_L, "1" })
    private static long mulAndAddToOverflowL(long a) {
        return a * Long.MAX_VALUE + a; // a*(MAX+1) = a*(MIN) = a<<63
    }

    // --- bit shift tests ---
    @Test
    @IR(failOn = {ADD_I, LSHIFT_I})
    private static int bitShiftToOverflow() {
        int i, x = 0;
        for (i = 0; i < 32; i++) {
            x = i;
        }

        // x = 31 (phi), i = 32 (phi + 1)
        return i + (x << i) + i; // Expects 32 + 31 + 32 = 95
    }

    @Test
    @IR(failOn = {ADD_L, LSHIFT_L})
    private static long bitShiftToOverflowL() {
        int i, x = 0;
        for (i = 0; i < 64; i++) {
            x = i;
        }

        // x = 63 (phi), i = 64 (phi + 1)
        return i + (x << i) + i; // Expects 64 + 63 + 64 = 191
    }

    // --- random tests ---
    private static final int CON1_I, CON2_I, CON3_I, CON4_I;
    private static final long CON1_L, CON2_L, CON3_L, CON4_L;

    static {
        CON1_I = GEN_INT.next();
        CON2_I = GEN_INT.next();
        CON3_I = GEN_INT.next();
        CON4_I = GEN_INT.next();

        CON1_L = GEN_LONG.next();
        CON2_L = GEN_LONG.next();
        CON3_L = GEN_LONG.next();
        CON4_L = GEN_LONG.next();
    }

    @Run(test = {
            "randomPowerOfTwoAddition",
            "randomPowerOfTwoAdditionL"
    })
    private void runRandomPowerOfTwoAddition() {
        for (int a : new int[] { 0, 1, Integer.MIN_VALUE, Integer.MAX_VALUE, GEN_INT.next() }) {
            Asserts.assertEQ(a * (CON1_I + CON2_I + CON3_I + CON4_I), randomPowerOfTwoAddition(a), "CON1_I=" + CON1_I + "; CON2_I=" + CON2_I + "; CON3_I=" + CON3_I + "; CON4_I=" + CON4_I);
        }

        for (long a : new long[] { 0, 1, Long.MIN_VALUE, Long.MAX_VALUE, GEN_LONG.next() }) {
            Asserts.assertEQ(a * (CON1_L + CON2_L + CON3_L + CON4_L), randomPowerOfTwoAdditionL(a), "CON1_L=" + CON1_L + "; CON2_L=" + CON2_L + "; CON3_L=" + CON3_L + "; CON4_L=" + CON4_L);
        }
    }

    // We can't do IR verification but only check for correctness for a better confidence.
    @Test
    private static int randomPowerOfTwoAddition(int a) {
        return a * CON1_I + a * CON2_I + a * CON3_I + a * CON4_I;
    }

    @Test
    private static long randomPowerOfTwoAdditionL(long a) {
        return a * CON1_L + a * CON2_L + a * CON3_L + a * CON4_L;
    }

    @Test
    @IR(counts = { ADD_I, "1", LSHIFT_I, "1" })
    private static int rightPrecedence(int a) {
        return a + (a + a);
    }

    @Test
    @IR(counts = { ADD_L, "1", LSHIFT_L, "1" })
    private static long rightPrecedenceL(long a) {
        return a + (a + a);
    }

    @Test
    @IR(failOn = ADD_I)
    @IR(counts = { LSHIFT_I, "1" })
    private static int rightPrecedenceShift(int a) {
        return a + (a << 1) + a; // a + a*2 + a == a * 4 => a<<2
    }

    @Test
    @IR(failOn = ADD_L)
    @IR(counts = { LSHIFT_L, "1" })
    private static long rightPrecedenceShiftL(long a) {
        return a + (a << 1) + a; // == a*4 => a<<2
    }

    @Test
    @IR(counts = { SUB_I, "1", LSHIFT_I, "1" })
    private static int complexShiftPattern(int a) {
        return a + (a << 1) + (a << 2); // == a + a*2 + a*4 == a*7 == a * (2^3 - 1) => a << 3 - a
    }

    @Test
    @IR(counts = { ADD_I, "1", LSHIFT_I, "2" })
    private static int complexShiftPatternAddNotSimplified(int a) {
        return (a << 1) + (a << 2); // do no simplify since the form a * (2^x + 2^y) is transformed into a << x + a << y
    }

    @Test
    @IR(counts = { ADD_I, "1", LSHIFT_I, "1" })
    private static int complexShiftPatternAddNotSimplified2(int a) {
        return (a << 5) + a; // special case of above with y == 0
    }

    @Test
    @IR(counts = { SUB_I, "1", LSHIFT_I, "2" })
    private static int complexShiftPatternSubNotSimplified(int a) {
        return (a << 6) - (a << 2); // do no simplify since the form a * (2^x - 2^y) is transformed into a << x - a << y
    }

    @Test
    @IR(counts = { SUB_I, "1", LSHIFT_I, "1" })
    private static int complexShiftPatternSubNotSimplified2(int a) {
        return (a << 5) - a; // special case of above with y == 0
    }

    @Test
    @IR(counts = { SUB_I, "1", LSHIFT_I, "2" })
    private static int complexShiftPatternSubNotSimplified3(int a) {
        return a * 60;  // 2^6 - 2^2 == 64 - 4 = 60. The simplification happens, and is not reverted
    }

    @Test
    @IR(failOn = { ADD_I }, counts = { LSHIFT_I, "1" })
    private static int nestedAddPattern(int a) {
        return (a + a) + (a + a); // == a * 4 => a << 2
    }

    @Test
    @IR(counts = { ADD_I, "1", LSHIFT_I, "1" })
    private static int complexPrecedence(int a) {
        return a + a + ((a + a) + a);  // This is a * 5 == a * (2^2 + 1) => a << 2 + a
    }

    @Test
    @IR(counts = { SUB_L, "1", LSHIFT_L, "1" })
    private static long complexShiftPatternL(long a) {
        return a + (a << 1) + (a << 2); // == a + a*2 + a*4 == a*7 == a * (2^3 - 1) => a << 3 - a
    }

    @Test
    @IR(failOn = { ADD_L}, counts = { LSHIFT_L, "1" })
    private static long nestedAddPatternL(long a) {
        return (a + a) + (a + a); // == a * 4 => a << 2
    }

    @Test
    @IR(counts = { ADD_L, "1", LSHIFT_L, "1" })
    private static long complexPrecedenceL(long a) {
        return a + a + ((a + a) + a);  // This is a * 5 == a * (2^2 + 1) => a << 2 + a
    }

    @Test
    @IR(failOn = { ADD_I, MUL_I, SUB_I })
    private static int simplifyToParam(int a, int b, int c) {
        return ((a + c) + (b + c)) - (a + (c + c));  // b
    }

    @Test
    @IR(failOn = { ADD_I, MUL_I, SUB_I })
    private static int simplifyToConst(int a, int b, int c) {
        return ((a + c) + (b + c)) - a - b - c - c;  // 0
    }

    @Test
    @IR(counts = { LSHIFT_I, "1" }, failOn = { ADD_I, SUB_I })
    private static int differenceOfConsecutivePowersOfTwo(int a) {
        return (a << 5) - (a << 4);  // a << 4
    }

    @Test
    @IR(counts = { LSHIFT_I, "1" }, failOn = { ADD_I, SUB_I })
    private static int differenceOfConsecutivePowersOfTwoWithNoise(int a, int b) {
        return ((a << 5) - b) - (a << 4) + b;  // a << 4
    }

    @Test
    @IR(counts = { ADD_I, "1", LSHIFT_I, "2" }, failOn = { SUB_I })
    private static int differenceOfAlmostConsecutivePowersOfTwo(int a) {
        return (a << 6) - (a << 4);  // (a << 5) + (a << 4)
    }

    @Test
    @IR(counts = { LSHIFT_I, "1" }, failOn = { ADD_I, SUB_I })
    private static int addingTwiceTheSamePowerOfTwo(int a) {
        return (a << 4) + (a << 4);  // (a << 5)
    }

    @Test
    @IR(counts = { MUL_I, "1" }, failOn = { ADD_I, SUB_I, LSHIFT_I })
    private static int addingTooManyPowersOfTwo(int a) {
        return (a << 6) + (a << 4) + (a << 2);  // a * 84; 84 = 0b1010100 => not a nice shape
    }

    @Test
    @IR(counts = { LSHIFT_I, "1" }, failOn = { ADD_I, SUB_I, MUL_I })
    private static int overflowInt1(int a) {
        return a * 0x7f_ff_ff_fe + (a << 1);  // a * (int_max - 1) + a * 2 = a * int_min = a * 0x80_00_00_00 = a << 31
    }

    @Test
    @IR(failOn = { ADD_I, SUB_I, MUL_I, LSHIFT_I })
    private static int overflowInt2(int a) {
        return a * 0x7f_ff_ff_fe + (a << 1) - a * 0x80_00_00_00;  // a * (int_max - 1) + a * 2 - a * int_min = 0
    }

    @Test
    @IR(counts = { LSHIFT_I, "1" }, failOn = { ADD_I, SUB_I, MUL_I })
    private static int overflowInt3(int a) {
        return a << 33;  // a << 33 = a << (32 + 1) = a << 1
    }

    @Test
    @IR(counts = { LSHIFT_I, "1" }, failOn = { ADD_I, SUB_I, MUL_I })
    private static int overflowInt4(int a) {
        int i = 33;
        int j = 0;
        do {
            i--;
            j++;
        } while (i > 0);
        return a << j;  // a << 33 = a << (32 + 1) = a << 1
    }

    @Test
    @IR(failOn = { ADD_I, SUB_I, MUL_I, LSHIFT_I })
    private static int overflowInt5(int a) {
        return ((a << 16) << 15) + (a << 31);  // a << 31 + a << 31 = a << 32 = a
    }

    @Test
    @IR(failOn = { ADD_I, SUB_I, MUL_I, LSHIFT_I })
    private static int overflowInt6(int a) {
        int i = 16;
        int j = 0;
        do {
            i--;
            j++;
        } while (i > 0);
        return ((a << j) * (1 << 15)) + (a << 31);  // a << 31 + a << 31 = a << 32 = a
    }

    @Test
    @IR(failOn = { ADD_I, SUB_I, MUL_I, LSHIFT_I })
    private static int overflowInt7(int a) {
        int i = 31;
        int j = 0;
        do {
            i--;
            j++;
        } while (i > 0);
        return (a << j) + a * 0x80_00_00_00;  // a << 31 + a * int_min = 0
    }

    @Test
    @IR(counts = { SUB_I, "1", LSHIFT_I, "2" }, failOn = { ADD_I, MUL_I })
    private static int sumInProduct(int a, int b) {
        int i = 10;
        int j = 0;
        do {
            i--;
            j++;
        } while (i > 0);
        return ((a + b) << j) + (a - (b << 1)) * 1_024;  // (a + b) * 1_024 + (a - 2*b) * 1_024 = a * 2_048 - b * 1_024 = a << 11 - b << 10
    }

    @Test
    @IR(counts = { ADD_I, "2" }, failOn = { SUB_I, MUL_I, LSHIFT_I })
    private static int complicated(int a, int b, int c, int d, int x, int y) {
        return
            (((a + (b << 37) - 10) * 3 - 3 - ((a << 33) + (b << -27) - 22) - y) << 33)
          + (((c * 6 - (d << 34) + 17 + x * 0 + 0 * y) << -30) * 7)
          + (((x + (y << 36) - 5) * 9 - ((x << 3) + (y << 6) - 40)) << 32)
          - (
                ((a + (b << 69) - 11) << 1)
              + ((b + (c << 34) - (d << 33) + 3 + y) << 6)
              - (((c << 4) - (d << 1) + 5 - 4 * c) * 7)
              - ((c - d + (((1 << 1337) * ((a + c + 1) * 8 - (a + c) * 9 + a + c)) << 2) + 9) << 2)
              - (((d * 1) << -31) - y)
              + (((1 * y) << -29) + (y << 34))
              + (1 << 8) + (1 << 7) + (1 << 3)
            );
        // x + y + (-42)
    }

}
