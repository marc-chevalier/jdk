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
 * @bug 8396039
 * @summary ReduceFieldZeroing doesn't check deep enough for dependent load and can lead to incorrect execution
 *
 * @run main ${test.main.class}
 */

package compiler.memoryinitialization.storeCapture;

public class TestStoreCaptureWithIndirectlyUsedMemory {
    static class Holder {
        Object value;
    }

    static final Object PRE_ALLOCATED_OBJECT = new Object();
    static final Holder PRE_ALLOCATED_HOLDER = new Holder();
    static {
        PRE_ALLOCATED_HOLDER.value = PRE_ALLOCATED_OBJECT;
    }

    static Holder sink;
    static Object test(boolean usePreAllocated, Holder preAllocated, Object fresh) {
        if (preAllocated == null) {
            throw new NullPointerException();
        }
        Holder holder = new Holder();
        // holder.value == null
        Holder selectedHolder = usePreAllocated ? preAllocated : holder;
        // usePreAllocated <=> selectedHolder.value != null
        Object result = selectedHolder.value;
        // usePreAllocated <=> result != null
        holder.value = fresh;
        // holder.value != null, so selectedHolder.value != null, but result shouldn't be changed
        // Let's use holder, so it's not optimized away
        sink = holder;
        return result;
    }

    public static void main(String[] args) {
        for (int i = 0; i < 100_000; i++) {
            boolean usePreAllocated = i % 2 == 0;
            Object expected = usePreAllocated ? PRE_ALLOCATED_OBJECT : null;
            Object fresh = new Object();
            Object result = test(usePreAllocated, PRE_ALLOCATED_HOLDER, fresh);
            if (result != expected) {
                throw new AssertionError(
                        "iteration=" + i +
                                ", usePreAllocated=" + usePreAllocated +
                                ", expected=" + expected +
                                ", result=" + result +
                                ", fresh=" + fresh
                );
            }
        }
    }
}
