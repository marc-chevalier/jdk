/*
 * @test
 * @modules java.base/jdk.internal.misc
 * @library /test/lib /
 * @run driver ${test.main.class}
 */

package compiler.loopopts.superword;
// --- IMPORTS start ---

import compiler.lib.ir_framework.*;
import jdk.test.lib.Utils;
import compiler.lib.verify.*;

import java.util.Random;
import java.lang.foreign.*;

// --- IMPORTS end   ---
public class AliasingFuzzer {
    // --- CLASS_HOOK insertions start ---
// --- CLASS_HOOK insertions end   ---
    public static void main(String[] vmFlags) {
        TestFramework framework = new TestFramework(AliasingFuzzer.class);
        // framework.addFlags("-classpath", "/opt/mach5/mesos/work_dir/slaves/4fd37682-a954-4334-9b98-1adbf11484c8-S19447/frameworks/1735e8a2-a1db-478c-8104-60c8b0af87dd-0196/executors/89eda66d-97da-4e96-ab58-691bed58b691/runs/8b76e314-4edf-4538-9d56-826bf5a61eeb/testoutput/test-support/jtreg_open_test_hotspot_jtreg_tier1_compiler_2/classes/2/compiler/loopopts/superword/TestAliasingFuzzer_vanilla.d:/opt/mach5/mesos/work_dir/jib-master/install/2026-09-04-0645201.marc.chevalier.jdk/src.full/open/test/hotspot/jtreg/compiler/loopopts/superword:/opt/mach5/mesos/work_dir/slaves/4fd37682-a954-4334-9b98-1adbf11484c8-S19447/frameworks/1735e8a2-a1db-478c-8104-60c8b0af87dd-0196/executors/89eda66d-97da-4e96-ab58-691bed58b691/runs/8b76e314-4edf-4538-9d56-826bf5a61eeb/testoutput/test-support/jtreg_open_test_hotspot_jtreg_tier1_compiler_2/classes/2/compiler/loopopts/superword/TestAliasingFuzzer_vanilla.d/test/lib:/opt/mach5/mesos/work_dir/jib-master/install/jtreg/8.3/1/bundles/jtreg-8.3+1.zip/jtreg/lib/jtreg.jar:/opt/mach5/mesos/work_dir/jib-master/install/jtreg/8.3/1/bundles/jtreg-8.3+1.zip/jtreg/lib/junit-platform-console-standalone-1.14.2.jar:/opt/mach5/mesos/work_dir/jib-master/install/jtreg/8.3/1/bundles/jtreg-8.3+1.zip/jtreg/lib/testng-7.3.0.jar:/opt/mach5/mesos/work_dir/jib-master/install/jtreg/8.3/1/bundles/jtreg-8.3+1.zip/jtreg/lib/jcommander-1.82.jar:/opt/mach5/mesos/work_dir/jib-master/install/jtreg/8.3/1/bundles/jtreg-8.3+1.zip/jtreg/lib/guice-5.1.0.jar:/opt/mach5/mesos/work_dir/slaves/4fd37682-a954-4334-9b98-1adbf11484c8-S19447/frameworks/1735e8a2-a1db-478c-8104-60c8b0af87dd-0196/executors/89eda66d-97da-4e96-ab58-691bed58b691/runs/8b76e314-4edf-4538-9d56-826bf5a61eeb/testoutput/test-support/jtreg_open_test_hotspot_jtreg_tier1_compiler_2/scratch/2/./compile-framework-classes-12251822815361628597");
        // framework.addFlags(vmFlags);
        framework.start();
    }

    // --- LIST OF TESTS start ---
    private static final Random RANDOM = Utils.getRandomInstance();

    public static record IndexForm(int con, int ivScale, int invar0Scale, int[] invarRestScales, int size) {
        public IndexForm {
            if (ivScale == 0 || invar0Scale == 0) {
                throw new RuntimeException("Bad scales: " + ivScale + " " + invar0Scale);
            }
        }

        public static record Range(int lo, int hi) {
            public Range {
                if (lo >= hi) {
                    throw new RuntimeException("Bad range: " + lo + " " + hi);
                }
            }
        }

        public int err() {
            int sum = 0;
            for (int scale : invarRestScales) {
                sum += Math.abs(scale);
            }
            return sum;
        }

        public int invar0ForIvLo(Range range, int ivLo) {
            if (ivScale > 0) {
                // index(iv) is smallest for iv = ivLo, so we must satisfy:
                //   range.lo <= con + iv.lo * ivScale + invar0 * invar0Scale + invarRest
                //            <= con + iv.lo * ivScale + invar0 * invar0Scale - err
                // It follows:
                //   invar0 * invar0Scale >= range.lo - con - iv.lo * ivScale + err
                int rhs = range.lo() - con - ivLo * ivScale + err();
                int invar0 = (invar0Scale > 0)
                        ?
                        // invar0 * invar0Scale >=  range.lo - con - iv.lo * ivScale + err
                        // invar0               >= (range.lo - con - iv.lo * ivScale + err) / invar0Scale
                        Math.floorDiv(rhs + invar0Scale - 1, invar0Scale) // round up division
                        :
                        // invar0 * invar0Scale >=  range.lo - con - iv.lo * ivScale + err
                        // invar0               <= (range.lo - con - iv.lo * ivScale + err) / invar0Scale
                        Math.floorDiv(rhs, invar0Scale); // round down division
                if (range.lo() > con + ivLo * ivScale + invar0 * invar0Scale - err()) {
                    throw new RuntimeException("sanity check failed (1)");
                }
                return invar0;
            } else {
                // index(iv) is largest for iv = ivLo, so we must satisfy:
                //   range.hi >= con + iv.lo * ivScale + invar0 * invar0Scale + invarRest + size
                //            >= con + iv.lo * ivScale + invar0 * invar0Scale + err       + size
                // It follows:
                //   invar0 * invar0Scale <= range.hi - con - iv.lo * ivScale - err - size
                int rhs = range.hi() - con - ivLo * ivScale - err() - size();
                int invar0 = (invar0Scale > 0)
                        ?
                        // invar0 * invar0Scale <= rhs
                        // invar0               <= rhs / invar0Scale
                        Math.floorDiv(rhs, invar0Scale) // round down division
                        :
                        // invar0 * invar0Scale <= rhs
                        // invar0               >= rhs / invar0Scale
                        Math.floorDiv(rhs + invar0Scale + 1, invar0Scale); // round up division
                if (range.hi() < con + ivLo * ivScale + invar0 * invar0Scale + err() + size()) {
                    throw new RuntimeException("sanity check failed (2)");
                }
                return invar0;

            }
        }

        public int ivHiForInvar0(Range range, int invar0) {
            if (ivScale > 0) {
                // index(iv) is largest for iv = ivHi, so we must satisfy:
                //   range.hi >= con + iv.hi * ivScale + invar0 * invar0Scale + invarRest + size
                //            >= con + iv.hi * ivScale + invar0 * invar0Scale + err       + size
                // It follows:
                //   iv.hi * ivScale <=  range.hi - con - invar0 * invar0Scale - err - size
                //   iv.hi           <= (range.hi - con - invar0 * invar0Scale - err - size) / ivScale
                int rhs = range.hi() - con - invar0 * invar0Scale - err() - size();
                int ivHi = Math.floorDiv(rhs, ivScale); // round down division
                if (range.hi() < con + ivHi * ivScale + invar0 * invar0Scale + err() + size()) {
                    throw new RuntimeException("sanity check failed (3)");
                }
                return ivHi;
            } else {
                // index(iv) is smallest for iv = ivHi, so we must satisfy:
                //   range.lo <= con + iv.hi * ivScale + invar0 * invar0Scale + invarRest
                //            <= con + iv.hi * ivScale + invar0 * invar0Scale - err
                // It follows:
                //   iv.hi * ivScale >=  range.lo - con - invar0 * invar0Scale + err
                //   iv.hi           <= (range.lo - con - invar0 * invar0Scale + err) / ivScale
                int rhs = range.lo() - con - invar0 * invar0Scale + err();
                int ivHi = Math.floorDiv(rhs, ivScale); // round down division
                if (range.lo() > con + ivHi * ivScale + invar0 * invar0Scale - err()) {
                    throw new RuntimeException("sanity check failed (4)");
                }
                return ivHi;

            }
        }
    }

    // --- test_853 start ---
// invarRest fields:
// Containers fields:
    private static MemorySegment original_container0_853 = MemorySegment.ofArray(new int[38756]);
    private static MemorySegment test_container0_853 = MemorySegment.ofArray(new int[38756]);
    private static MemorySegment reference_container0_853 = MemorySegment.ofArray(new int[38756]);
    private static MemorySegment original_container1_853 = MemorySegment.ofArray(new int[38756]);
    private static MemorySegment test_container1_853 = MemorySegment.ofArray(new int[38756]);
    private static MemorySegment reference_container1_853 = MemorySegment.ofArray(new int[38756]);
    // Index forms for the accesses:
    private static IndexForm index0_853 = new IndexForm(45400, 1, -4, new int[]{}, 1);
    private static IndexForm index1_853 = new IndexForm(-65787, 3, 1, new int[]{}, 1);
    // Count the run invocations.
    private static int iterations_853 = 0;

    @Run(test = "test_853")
    @Warmup(100)
    public static void run_853(RunInfo info) {

        // Once warmup is over (100x), repeat 10x to get reasonable coverage of the
        // randomness in the tests.
        int reps = info.isWarmUp() ? 10 : 1;
        for (int r = 0; r < reps; r++) {

            iterations_853++;
// Init containers from original data:
            test_container0_853.copyFrom(original_container0_853);
            reference_container0_853.copyFrom(original_container0_853);
            test_container1_853.copyFrom(original_container1_853);
            reference_container1_853.copyFrom(original_container1_853);
// Container aliasing:
            var test_0 = (iterations_853 % 2 == 0) ? test_container0_853 : test_container0_853;
            var reference_0 = (iterations_853 % 2 == 0) ? reference_container0_853 : reference_container0_853;
            var test_1 = (iterations_853 % 2 == 0) ? test_container1_853 : test_container1_853;
            var reference_1 = (iterations_853 % 2 == 0) ? reference_container1_853 : reference_container1_853;
// Generate ranges:
            int middle = RANDOM.nextInt(19378 / 3, 19378 * 2 / 3);
            int rnd = Math.min(256, 19378 / 10);
            int range = 19378 / 3 - RANDOM.nextInt(rnd);
            var r0 = new IndexForm.Range(middle - range, middle);
            var r1 = new IndexForm.Range(middle, middle + range);
            if (RANDOM.nextBoolean()) {
                var tmp = r0;
                r0 = r1;
                r1 = tmp;
            }
// Compute loop bounds and loop invariants.
            int ivLo = RANDOM.nextInt(-1000, 1000);
            int ivHi = ivLo + 155024;
            int invar0_0 = index0_853.invar0ForIvLo(r0, ivLo);
            ivHi = Math.min(ivHi, index0_853.ivHiForInvar0(r0, invar0_0));
            int invar0_1 = index1_853.invar0ForIvLo(r1, ivLo);
            ivHi = Math.min(ivHi, index1_853.ivHiForInvar0(r1, invar0_1));
// Let's check that the range is large enough, so that the vectorized
// main loop can even be entered.
            if (ivLo + 1000 > ivHi) {
                throw new RuntimeException("iv range too small: " + ivLo + " " + ivHi);
            }
// Verify the bounds we just created, just to be sure there is no unexpected aliasing!
            int i = ivLo;
            int lo_0 = (int) (45400 + 1 * i + -4 * invar0_0);
            int lo_1 = (int) (-65787 + 3 * i + 1 * invar0_1);
            i = ivHi;
            int hi_0 = (int) (45400 + 1 * i + -4 * invar0_0);
            int hi_1 = (int) (-65787 + 3 * i + 1 * invar0_1);
// Aliasing unknown, cannot verify bounds.
            // Run test and compare with interpreter results.
            var result = test_853(test_0, invar0_0, test_1, invar0_1, ivLo, ivHi);
            var expected = reference_853(reference_0, invar0_0, reference_1, invar0_1, ivLo, ivHi);
            Verify.checkEQ(result, expected);
        } // end reps
    } // end run_853

    @Test
// Unfortunately, there are some issues that prevent RangeCheck elimination.
// The cases are currently quite unpredictable, so we cannot create any IR
// rules - sometimes there are vectors sometimes not.
// Aliasing check should never fail at runtime, so the predicate
// should never fail, and we do not have to use multiversioning.
// Failure could have a few causes:
// - issues with doing RCE / missing predicates
//   -> other loop-opts need to be fixed
// - predicate fails: recompile with multiversioning
//   -> logic in runtime check may be wrong
    @IR(counts = {".*multiversion.*", "= 0"},
            phase = CompilePhase.PRINT_IDEAL,
            applyIf = {"UseAutoVectorizationPredicate", "true"},
            applyIfPlatform = {"64-bit", "true"},
            applyIfCPUFeatureOr = {"sse4.1", "true", "asimd", "true"})
    public static Object test_853(MemorySegment container_0, long invar0_0, MemorySegment container_1, long invar0_1, long ivLo, long ivHi) {
        for (long i = ivLo; i < ivHi; i += 1) {
            container_0.setAtIndex(ValueLayout.JAVA_DOUBLE_UNALIGNED, 45400L + 1L * i + -4L * invar0_0, (double) 0x0102030405060708L);
            container_1.setAtIndex(ValueLayout.JAVA_DOUBLE_UNALIGNED, -65787L + 3L * i + 1L * invar0_1, (double) 0x1112131415161718L);
        }
        return new Object[]{
                container_0, container_1
        };
    }

    @DontCompile
    public static Object reference_853(MemorySegment container_0, long invar0_0, MemorySegment container_1, long invar0_1, long ivLo, long ivHi) {
        for (long i = ivLo; i < ivHi; i += 1) {
            container_0.setAtIndex(ValueLayout.JAVA_DOUBLE_UNALIGNED, 45400L + 1L * i + -4L * invar0_0, (double) 0x0102030405060708L);
            container_1.setAtIndex(ValueLayout.JAVA_DOUBLE_UNALIGNED, -65787L + 3L * i + 1L * invar0_1, (double) 0x1112131415161718L);
        }
        return new Object[]{
                container_0, container_1
        };
    }

    // --- test_853 end ---
}