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
 * @bug 8389700
 * @summary Test StoreLSpecial are captured
 * @enablePreview
 * @modules java.base/jdk.internal.value
 *          java.base/jdk.internal.vm.annotation
 * @library /test/lib /
 * @run driver ${test.main.class}
 */

package compiler.valhalla.valuetypes;

import compiler.lib.ir_framework.*;
import jdk.internal.vm.annotation.NullRestricted;

import static compiler.lib.ir_framework.IRNode.*;

public class TestStoreLSpecialCapture {
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
                        "--add-exports", "java.base/jdk.internal.misc=ALL-UNNAMED",
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

    @Test
    @IR(applyIf = {"UseCompressedOops", "false"},
        failOn = {STORE_L_SPECIAL})
    @IR(applyIfAnd = {"UseCompressedOops", "true", "ReduceFieldZeroing", "true"},
        counts = {STORE_L_SPECIAL_RAW_MEMORY, "1"})
    @IR(applyIfAnd = {"UseCompressedOops", "true", "ReduceFieldZeroing", "false"},
        counts = {STORE_L_SPECIAL_BOTTOM_MEMORY, "1"})
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

    @Test
    @IR(applyIf = {"UseCompressedOops", "false"},
        failOn = {STORE_L_SPECIAL})
    @IR(applyIf = {"UseCompressedOops", "true"},
        counts = {STORE_L_SPECIAL_BOTTOM_MEMORY, "1"})
    static HolderWithTwoOops test2(HolderWithTwoOops h, MyValueWithTwoOops v) {
        var _ = v.v1;  // Force v != null
        h.v = v;
        return h;
    }

    @Run(test={"test2"})
    public void test2_verifier() {
        MyValueWithTwoOops v = new MyValueWithTwoOops(new Object(), new Object());
        HolderWithTwoOops h = new HolderWithTwoOops();
        test2(h, v);
    }
}
