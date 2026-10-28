Resolver retention simplifications: full-ctest follow-up
2026-10-26

Decision, 2026-10-28

Drop interface-reachability pruning and its ownership-tracking machinery. The
compiler implementation is restored exactly to 550a374e4, preserving the earlier
lifetime cleanups. Keep the measurements below as the record of the discarded
experiment; "final build" below means the measured experimental ced10d57e, not
the implementation selected for the PR. The restoration is not re-benchmarked.

Against the historical pre-pruning build, the optimized experiment still cost
16.1% more time and 3.6% more allocation, with essentially identical retained
session heap (315.8 versus 315.3 MiB). Its benefit on synthetic unused private
bodies did not justify the ongoing bookkeeping and design complexity on ctest.
The useful pre-pruning cleanups reduced retained heap from 349.7 to 315.3 MiB
and allocation from 8396.2 to 8142.0 MiB; their small timing change is not evidence
of an established speedup. All comparisons remain subject to the caveats below.

Remove the reachability traversal, reader/writer tracking, body ownership in
contexts and listeners, tracked/completed cache variants, and pruning flags.
Module finalization still detaches pending observers and releases the temporary
workspace. Compiled artifacts still release elaborators, compiler contexts,
diagnostic collectors and reference-interning builders. Graph routing continues
to preserve intermediate exporters and isolate each consumer's mutations.

Keep all MLscript behavior regressions and the cyclic re-export graph-growth
test. Remove the tests requiring bounded retention of unused private bodies,
bounded ownership metadata, and sharing of owned execution views: their tested
machinery is gone. Keep the whole-artifact retention and importer-isolation
tests. Private bodies' inference graphs can again remain in a compiled unit;
more selective retention would need representative memory savings and a cheaper
design, potentially based on lazy body inference, before being reconsidered.

Validation after removal: hkmc2AllTests/test passed on 2026-10-28 (116 seconds),
including the retained regression and graph-growth tests. Metals compilation
also passed. No golden output changed.

Results (MiB = 1,048,576 bytes; cumulative stages)

Revision   Stage                         Seconds  Fork-mean range  Allocated MiB  Retained MiB
f6cce3eca  Previous final (historical)    6.595  6.577-6.598         9671.2       338.3
b0b30e3f7  1. Callable listeners          6.524  6.463-6.559         9379.4       320.8
20090641b  2. Entry tracking              5.966  5.957-6.015         8620.8       320.8
ced10d57e  3. Shared graphs               5.869  5.811-5.923         8436.2       315.8

Stage-to-stage changes:
  b0b30e3f7: time -1.1%, allocation -3.0%, retained heap -5.2%.
  20090641b: time -8.6%, allocation -8.1%, retained heap +0.0%.
  ced10d57e: time -1.6%, allocation -2.1%, retained heap -1.6%.
  The step-1 comparison uses historical measurements; steps 2 and 3 use the current experiment.

Final build relative to historical references:
  f6cce3eca (interface-pruning): time -11.0%, allocation -12.8%, retained heap -6.7%.
  550a374e4 (workspace-release): time +16.1%, allocation +3.6%, retained heap +0.2%.
  8feafb6a1 (baseline): time +13.7%, allocation +0.5%, retained heap -9.7%.

All 180 full timing suites completed (108 warmups, 72 measured), plus nine
separate full-suite heap observations. No old compiler build was rerun.

Interpretation

The entry-tracking change provides the clear time reduction within this experiment
(-8.6%) and saves 8.1% of allocation. Callable listener objects remove most of the
extra retained listener representation; sharing graph origins removes another
5.0 MiB. Entry tracking changes retained heap by only +47.1 KiB per session:
its two storage modes have a small fixed per-table cost, with no retained tracking
record per entry. The final retained session is about 22.5 MiB below the historical
pruning build, and about 0.5 MiB above the historical pre-pruning build.

The 1.1% and 1.6% adjacent timing changes in steps 1 and 3 are small. Do not treat
them as established speedups: there are only three forks, the schedule is shuffled
but not counterbalanced, and GC/JIT work continues in measured batches. JIT time
averages about 241-244 ms per measured suite. The final build's last four measured
batches are 0.3-1.5% slower than its first four: their GC counter increases by
126-133 ms per suite while JIT time falls by 63-72 ms. The mean over all eight
measured batches includes those collections; no samples or GC costs are removed.

The changes recover much of the pruning overhead, but do not eliminate it.
The historical pre-pruning comparison still shows +16.1% elapsed time and +3.6%
allocation, with essentially the same retained heap on this corpus. Timing
comparisons with that earlier run retain the temporal-variation caveat. Tracking
ownership and computing the conservative reachable graph still cost work. More
precise/lazy inference could improve pruning, but these measurements do not
establish how much of the remaining time any further change would recover.

Three cumulative changes, each committed after hkmc2AllTests/test passed:
  b0b30e3f7  Fuse listener ownership and routing into callable listener objects.
  20090641b  Keep temporary ownership on active cache entries and publisher data;
             discard it when finalization selects the retained graph.
  ced10d57e  Share graph/substitution origins independently of body ownership;
             keep owned execution views out of persistent keys and listener origins.

Correctness coverage

ResolverRetention.mls exercises a re-exported callback entering consumer code
which calls the defining library again, under two nominal generic activations.
It also exercises two bodies waiting on one forward alias before their callbacks
can be checked. PublisherTest bounds copied hosts and listener growth through
five re-export boundaries and repeated cyclic publications. ResolverRetentionTest
checks bounded tracking on repeated shared-cache reads, metadata release after
pruning, and 2,000 registrations sharing their graph without retaining owned
execution views; each callback must still receive its own body owner. Existing
whole-artifact reference walks, dead-body growth, importer isolation and cyclic
inference tests remain enabled. All golden changes are included in the commits.

Design and remaining costs

Reader/writer tracking has no parallel table of inference keys. Cache hits update
metadata on the entry already found. Active caches use tracked values; completed
caches contain plain values, and completed edge tables contain plain sets. A
publisher has one nullable metadata reference which is cleared at finalization.
The finalization worklists are temporary and released with the workspace.

Graph keys and listener origins store ResolutionContext.Graph. Body ownership
is a transient execution view; a listener stores its owner symbol alongside its
shared origin. Graph equality and substitution behavior do not depend on that
owner. Imports still preserve every intermediate exporter's private graph.
There is no new owner-context interning table or mutable current-owner variable.

The read/producer dependency closure remains conservative. An unreachable body
which has already supplied inference to live code may therefore remain reachable.
Removing that overapproximation would require more precise dependency or lazy
body inference, not simply dropping callbacks based on syntactic reachability.
Owned views still allocate during execution; the improvement is sharing retained
graph origins and reducing transient payload. Registration/import wrappers and
reader/writer sets still have costs. Publisher metadata also leaves one null field
in the retained object layout. These costs are measured, not assumed away.

Protocol

Uses hkmc2Benchmarks/bench_resolver_suite.py and ResolverSuiteBenchmark unchanged.
Only the three NEW compiler JARs were measured; no previous commit was rerun.
The same 58 ctest cases run sequentially in sorted order, using a fresh shared
CompilerCtx per full suite, including prelude/runtime compilation and JS writes.
The complete ctest manifest and all compilation inputs are unchanged. The overall
tracked-.mls hash differs because the worksheet regression file changed; that
file is outside the measured ctest corpus.

Three timing JVMs per stage, with 12 full-suite warmups and eight measured suites
per JVM. One JVM at a time, stage order shuffled within rounds with seed 582.
  -Xms1g -Xmx1g -Xss8m -XX:ActiveProcessorCount=1 -XX:+UseSerialGC -Xbatch
Own SBT shell was stopped before measurements. The JVM sees one processor and
uses serial GC and foreground compilation. macOS controls physical core placement;
the process is not pinned. Allocation uses JVM-wide getTotalThreadAllocatedBytes.
Wall time, process CPU, allocation, GC and JIT counters are all saved per suite.

Three separate fresh JVMs per stage measure retained session heap. Each compiles
one full suite and takes fully compacting post-GC heap-pool collection snapshots
with its CompilerCtx held, then released; a weak reference must clear. These runs
add -XX:MarkSweepAlwaysCompactCount=1 and contribute no timing observations.

For timing and allocation: average eight measured suites within each fork, then
report the median of the three fork means, with their range. Retained heap is the
median of three separate heap runs. Fork ranges are not confidence intervals.
Small timing differences require caution; within-fork warmup drift is reported.
Historical references come unchanged from ../resolver-ctest-2026-10-26/summary.csv.
They were measured in a different run, so timing comparisons to them cannot fully
separate code changes from temporal machine variation.

Reproduce (from a build archive containing builds.json, classpath.txt and JARs):
  python3 hkmc2Benchmarks/bench_resolver_suite.py timing <repo> <archive> <timing-output>
  python3 hkmc2Benchmarks/bench_resolver_suite.py heap <repo> <archive> <heap-output>
  python3 hkmc2Benchmarks/results/resolver-ctest-2026-10-26/summarize.py <timing-output> <heap-output>/retained-heap.csv

Raw samples, per-fork means, per-stage summaries, retained-heap observations and
run metadata are included alongside this report. comparison.csv includes the
historical prior build and current cumulative stages; summary.csv contains only
the newly measured stages.
