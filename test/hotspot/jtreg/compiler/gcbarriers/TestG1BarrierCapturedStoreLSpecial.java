/*
 * Copyright (c) 2026, Oracle and/or its affiliates. All rights reserved.
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

/*
 * @test
 * @bug 8389700 8387705
 * @summary Test that G1 barriers for StoreLSpecial are generated and optimized as expected
 * @enablePreview
 * @modules java.base/jdk.internal.value
 *          java.base/jdk.internal.vm.annotation
 * @library /test/lib /
 * @requires vm.gc.G1
 * @run driver ${test.main.class}
 */

package compiler.gcbarriers;

import compiler.lib.ir_framework.*;
import jdk.internal.vm.annotation.NullRestricted;

import static compiler.lib.ir_framework.IRNode.*;

public class TestG1BarrierCapturedStoreLSpecial {
    static final String PRE_ONLY = "pre";
    static final String PRE_AND_POST = "pre post";
    static final String PRE_AND_POST_NOT_NULL = "pre post notnull";
    static final String ANY = ".*";

    public static void main(String[] args) {
        TestFramework framework = new TestFramework();
        Scenario[] scenarios = new Scenario[2*2];
        int scenarioIndex = 0;
        for (int i = 0; i < 2; i++) {
            for (int j = 0; j < 2; j++) {
                scenarios[scenarioIndex] =
                    new Scenario(scenarioIndex,
                                 "--enable-preview",
                                 "-XX:" + (i == 0 ? "-" : "+") + "UseCompressedOops",
                                 "-XX:" + (j == 0 ? "-" : "+") + "ReduceFieldZeroing"
                            );
                scenarioIndex++;
            }
        }
        framework.addScenarios(scenarios)
                .addFlags(
                        "--add-exports", "java.base/jdk.internal.value=ALL-UNNAMED",
                        "--add-exports", "java.base/jdk.internal.vm.annotation=ALL-UNNAMED"
                )
                .start();
    }

    static value class MyValue {
        Object value;

        MyValue(Object value) {
            this.value = value;
        }
    }

    static class Holder {
        Integer i = null;
        MyValue v = null;
    }

    static value class MyValueWithTwoOops {
        Object v1;
        Object v2;

        MyValueWithTwoOops(Object v1, Object v2) {
            this.v1 = v1;
            this.v2 = v2;
        }
    }

    static class HolderWithTwoOops {
        @NullRestricted
        MyValueWithTwoOops v;

        HolderWithTwoOops() {
            this.v = new MyValueWithTwoOops(null, null);
            super();
        }
        HolderWithTwoOops(MyValueWithTwoOops v) {
            this.v = v;
            super();
        }
    }

    static abstract value class MyValueOopFirstBase {
        Object v;

        MyValueOopFirstBase(Object v) {
            this.v = v;
        }
    }
    static value class MyValueOopFirst extends MyValueOopFirstBase {
        int i;

        MyValueOopFirst(int i, Object v) {
            this.i = i;
            super(v);
        }
    }
    static class HolderWithOopsFirst {
        @NullRestricted
        MyValueOopFirst v;

        HolderWithOopsFirst() {
            this.v = new MyValueOopFirst(0, null);
            super();
        }
        HolderWithOopsFirst(MyValueOopFirst v) {
            this.v = v;
            super();
        }
    }

    static abstract value class MyValueOopSecondBase {
        int i;

        MyValueOopSecondBase(int i) {
            this.i = i;
        }
    }
    static value class MyValueOopSecond extends MyValueOopSecondBase {
        Object v;

        MyValueOopSecond(int i, Object v) {
            this.v = v;
            super(i);
        }
    }
    static class HolderWithOopsSecond {
        @NullRestricted
        MyValueOopSecond v;

        HolderWithOopsSecond() {
            this.v = new MyValueOopSecond(0, null);
            super();
        }
        HolderWithOopsSecond(MyValueOopSecond v) {
            this.v = v;
            super();
        }
    }

    @Test
    @IR(applyIf = {"UseCompressedOops", "false"},
        failOn = {G1_STORE_L_SPECIAL})
    @IR(applyIfAnd = {"UseCompressedOops", "true", "ReduceFieldZeroing", "true"},
        counts = {G1_STORE_L_SPECIAL, "1"},
        failOn = {G1_STORE_L_SPECIAL_WITH_BARRIER_FLAG, ANY})
    @IR(applyIfAnd = {"UseCompressedOops", "true", "ReduceFieldZeroing", "false"},
        counts = {G1_STORE_L_SPECIAL_WITH_BARRIER_FLAG, PRE_AND_POST, "1"})
    static Holder test1(Integer i, MyValue v) {
        Holder t = new Holder();
        t.i = i;
        t.v = v;
        return t;
    }

    @Run(test={"test1"})
    public void test1_verifier() {
        MyValue v = new MyValue(new Object());
        test1(42, v);
    }

    @Test
    @IR(applyIf = {"UseCompressedOops", "false"},
        failOn = {G1_STORE_L_SPECIAL})
    @IR(applyIfAnd = {"UseCompressedOops", "true", "ReduceFieldZeroing", "true"},
        counts = {G1_STORE_L_SPECIAL, "1"},
        failOn = {G1_STORE_L_SPECIAL_WITH_BARRIER_FLAG, ANY})
    @IR(applyIfAnd = {"UseCompressedOops", "true", "ReduceFieldZeroing", "false"},
        counts = {G1_STORE_L_SPECIAL_WITH_BARRIER_FLAG, PRE_AND_POST_NOT_NULL, "1"})
    static Holder test2(Integer i) {
        MyValue v = new MyValue(new Object());
        Holder t = new Holder();
        t.i = i;
        t.v = v;
        return t;
    }

    @Run(test={"test2"})
    public void test2_verifier() {
        test2(42);
    }

    @Test
    @IR(applyIf = {"UseCompressedOops", "false"},
        failOn = {G1_STORE_L_SPECIAL})
    @IR(applyIfAnd = {"UseCompressedOops", "true", "ReduceFieldZeroing", "true"},
        counts = {G1_STORE_L_SPECIAL, "1"},
        failOn = {G1_STORE_L_SPECIAL_WITH_BARRIER_FLAG, ANY})
    @IR(applyIfAnd = {"UseCompressedOops", "true", "ReduceFieldZeroing", "false"},
        counts = {G1_STORE_L_SPECIAL_WITH_BARRIER_FLAG, PRE_ONLY, "1"})
    static Holder test3(Integer i) {
        Holder t = new Holder();
        t.i = i;
        t.v = null;
        return t;
    }

    @Run(test={"test3"})
    public void test3_verifier() {
        test3(42);
    }

    @Test
    @IR(applyIf = {"UseCompressedOops", "false"},
        failOn = {G1_STORE_L_SPECIAL})
    @IR(applyIf = {"UseCompressedOops", "true"},
        counts = {G1_STORE_L_SPECIAL_TWO_OOPS_WITH_BARRIER_FLAG, PRE_AND_POST, "1"})
    static HolderWithTwoOops test4(HolderWithTwoOops h, MyValueWithTwoOops v) {
        var _ = v.v1;  // Force v != null
        h.v = v;
        return h;
    }

    @Run(test={"test4"})
    public void test4_verifier() {
        MyValueWithTwoOops v = new MyValueWithTwoOops(new Object(), new Object());
        HolderWithTwoOops h = new HolderWithTwoOops();
        test4(h, v);
    }

    @Test
    @IR(applyIf = {"UseCompressedOops", "false"},
        failOn = {G1_STORE_L_SPECIAL})
    @IR(applyIf = {"UseCompressedOops", "true"},
        counts = {G1_STORE_L_SPECIAL_TWO_OOPS_WITH_BARRIER_FLAG, PRE_AND_POST_NOT_NULL, "1"})
    static HolderWithTwoOops test5(HolderWithTwoOops h) {
        MyValueWithTwoOops v = new MyValueWithTwoOops(new Object(), new Object());
        h.v = v;
        return h;
    }

    @Run(test={"test5"})
    public void test5_verifier() throws NoSuchFieldException {
        HolderWithTwoOops h = new HolderWithTwoOops();
        test5(h);
    }

    @Test
    @IR(applyIf = {"UseCompressedOops", "false"},
        failOn = {G1_STORE_L_SPECIAL})
    @IR(applyIf = {"UseCompressedOops", "true"},
        counts = {G1_STORE_L_SPECIAL_TWO_OOPS_WITH_BARRIER_FLAG, PRE_AND_POST, "1"})
    static HolderWithTwoOops test6(HolderWithTwoOops h) {
        MyValueWithTwoOops v = new MyValueWithTwoOops(new Object(), null);
        h.v = v;
        return h;
    }

    @Run(test={"test6"})
    public void test6_verifier() throws NoSuchFieldException {
        HolderWithTwoOops h = new HolderWithTwoOops();
        test6(h);
    }

    @Test
    @IR(applyIf = {"UseCompressedOops", "false"},
        failOn = {G1_STORE_L_SPECIAL})
    @IR(applyIf = {"UseCompressedOops", "true"},
        counts = {G1_STORE_L_SPECIAL_TWO_OOPS_WITH_BARRIER_FLAG, PRE_AND_POST, "1"})
    static HolderWithTwoOops test7(HolderWithTwoOops h) {
        MyValueWithTwoOops v = new MyValueWithTwoOops(null, new Object());
        h.v = v;
        return h;
    }

    @Run(test={"test7"})
    public void test7_verifier() throws NoSuchFieldException {
        HolderWithTwoOops h = new HolderWithTwoOops();
        test7(h);
    }

    @Test
    @IR(applyIf = {"UseCompressedOops", "false"},
        failOn = {G1_STORE_L_SPECIAL})
    @IR(applyIf = {"UseCompressedOops", "true"},
        counts = {G1_STORE_L_SPECIAL_TWO_OOPS_WITH_BARRIER_FLAG, PRE_ONLY, "1"})
    static HolderWithTwoOops test8(HolderWithTwoOops h) {
        MyValueWithTwoOops v = new MyValueWithTwoOops(null, null);
        h.v = v;
        return h;
    }

    @Run(test={"test8"})
    public void test8_verifier() throws NoSuchFieldException {
        HolderWithTwoOops h = new HolderWithTwoOops();
        test8(h);
    }

    @Test
    @IR(applyIf = {"UseCompressedOops", "false"},
        failOn = {G1_STORE_L_SPECIAL})
    @IR(applyIf = {"UseCompressedOops", "true"},
        counts = {G1_STORE_L_SPECIAL_ONE_OOP_0_WITH_BARRIER_FLAG, PRE_AND_POST_NOT_NULL, "1"})
    static HolderWithOopsFirst test9(HolderWithOopsFirst h) {
        MyValueOopFirst v = new MyValueOopFirst(42, new Object());
        h.v = v;
        return h;
    }

    @Run(test={"test9"})
    public void test9_verifier() throws NoSuchFieldException {
        HolderWithOopsFirst h = new HolderWithOopsFirst();
        test9(h);
    }

    @Test
    @IR(applyIf = {"UseCompressedOops", "false"},
        failOn = {G1_STORE_L_SPECIAL})
    @IR(applyIf = {"UseCompressedOops", "true"},
        counts = {G1_STORE_L_SPECIAL_ONE_OOP_4_WITH_BARRIER_FLAG, PRE_AND_POST_NOT_NULL, "1"})
    static HolderWithOopsSecond test10(HolderWithOopsSecond h) {
        MyValueOopSecond v = new MyValueOopSecond(42, new Object());
        h.v = v;
        return h;
    }

    @Run(test={"test10"})
    public void test10_verifier() throws NoSuchFieldException {
        HolderWithOopsSecond h = new HolderWithOopsSecond();
        test10(h);
    }
}
