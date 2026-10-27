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
 * @summary Test that StoreLSpecial capture preserves reads
 * @enablePreview
 * @modules java.base/jdk.internal.misc
 * @library /test/lib /
 * @requires vm.gc.G1 & vm.bits == 64
 * @run driver ${test.main.class}
 */

package compiler.valhalla.valuetypes;

import java.lang.reflect.Field;

import compiler.lib.ir_framework.IR;
import compiler.lib.ir_framework.Run;
import compiler.lib.ir_framework.Test;
import compiler.lib.ir_framework.TestFramework;
import jdk.internal.misc.Unsafe;
import jdk.test.lib.Asserts;

import static compiler.lib.ir_framework.IRNode.STORE_L_SPECIAL_BOTTOM_MEMORY;
import static compiler.lib.ir_framework.IRNode.STORE_L_SPECIAL_RAW_MEMORY;

public class TestStoreLSpecialCaptureWriteReadWrite {
    private static final Unsafe UNSAFE = Unsafe.getUnsafe();
    private static final long REFERENCE_OFFSET;
    private static final long TAG_OFFSET;

    public static void main(String[] args) {
        TestFramework.runWithFlags(
                "--add-exports", "java.base/jdk.internal.misc=ALL-UNNAMED",
                "--enable-preview",
                "-Xmx1g",
                "-XX:+UseG1GC",
                "-XX:+UseCompressedOops",
                "-XX:+UseFieldFlattening",
                "-XX:+UseNullableAtomicValueFlattening",
                "-XX:+ReduceFieldZeroing");
    }

    static value class MyValue {
        Object reference;
        byte tag;

        MyValue(Object reference, byte tag) {
            this.reference = reference;
            this.tag = tag;
        }
    }

    static class Holder {
        MyValue value;
    }

    static {
        try {
            Field valueField = Holder.class.getDeclaredField("value");
            Asserts.assertTrue(!UNSAFE.isFlatField(valueField));
            long valueOffset = UNSAFE.objectFieldOffset(valueField);
            long valueHeaderSize = UNSAFE.valueHeaderSize(MyValue.class);
            // Translate buffered Value field offsets into offsets in Holder's flat payload.
            REFERENCE_OFFSET = valueOffset
                    + UNSAFE.objectFieldOffset(MyValue.class.getDeclaredField("reference"))
                    - valueHeaderSize;
            TAG_OFFSET = valueOffset
                    + UNSAFE.objectFieldOffset(MyValue.class.getDeclaredField("tag"))
                    - valueHeaderSize;
        } catch (NoSuchFieldException e) {
            throw new RuntimeException(e);
        }
    }

    static Holder sink;

    @Test
    @IR(counts = {
            STORE_L_SPECIAL_RAW_MEMORY, "1",
            STORE_L_SPECIAL_BOTTOM_MEMORY, "1"
    })
    static Object testSameAlias(Object first, Object second) {
        Holder holder = new Holder();
        holder.value = new MyValue(first, (byte) 17);
        Object result = UNSAFE.getReference(holder, REFERENCE_OFFSET);
        holder.value = new MyValue(second, (byte) 34);
        sink = holder;
        return result;
    }

    @Run(test = "testSameAlias")
    public void runSameAlias() {
        Object first = new Object();
        Object second = new Object();
        Asserts.assertEQ(first, testSameAlias(first, second));
    }

    @Test
    @IR(counts = {
            STORE_L_SPECIAL_RAW_MEMORY, "1",
            STORE_L_SPECIAL_BOTTOM_MEMORY, "1"
    })
    static byte testSecondLeaf(Object first, Object second) {
        Holder holder = new Holder();
        holder.value = new MyValue(first, (byte) 17);
        byte result = UNSAFE.getByte(holder, TAG_OFFSET);
        holder.value = new MyValue(second, (byte) 34);
        sink = holder;
        return result;
    }

    @Run(test = "testSecondLeaf")
    public void runSecondLeaf() {
        byte result = testSecondLeaf(new Object(), new Object());
        Asserts.assertEQ((byte) 17, result);
    }
}
