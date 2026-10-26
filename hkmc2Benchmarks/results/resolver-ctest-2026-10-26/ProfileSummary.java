import java.nio.file.*;
import java.io.*;
import java.util.*;
import java.time.Instant;
import jdk.jfr.consumer.*;

public class ProfileSummary {
  static String normalized(String s) { return s.replace('/', '.'); }
  static List<String> frames(RecordedEvent e) {
    var trace = e.getStackTrace();
    if (trace == null) return List.of();
    return trace.getFrames().stream().map(f -> normalized(f.getMethod().getType().getName()) + "." + f.getMethod().getName()).toList();
  }
  static String category(List<String> frames) {
    // Disjoint inclusive-stack categories; finalization takes precedence over
    // the same bookkeeping helpers used during inference. These are sampled
    // Java execution/allocation sites, not a decomposition of total wall time.
    if (frames.stream().anyMatch(s -> s.contains("ResolutionReachability") || s.contains("NewResolverState.finish") || s.contains("ResolutionRetention.close") || s.contains("ResolutionRetention.finish") || s.contains("ResolutionRetention.retained"))) return "finalization";
    if (frames.stream().anyMatch(s -> s.contains("ResolutionRetention"))) return "retention-bookkeeping";
    if (frames.stream().anyMatch(s -> s.contains("ResolutionContext.forCode"))) return "code-context";
    if (frames.stream().anyMatch(s -> s.contains("ResolutionContext.inGraph") || s.contains("ResolutionContext.withInstances") || s.contains("ResolutionContext.rebase") || s.contains("ResolutionContext.base"))) return "graph-context";
    return "other";
  }
  static void add(Map<String, long[]> values, String key, long amount) {
    var counts = values.computeIfAbsent(key, k -> new long[2]);
    counts[0]++;
    counts[1] += amount;
  }
  static String cell(Object value) { return "\"" + value.toString().replace("\"", "\"\"") + "\""; }
  static void row(PrintWriter out, Object... values) {
    out.println(Arrays.stream(values).map(ProfileSummary::cell).reduce((a,b) -> a + "," + b).orElse(""));
  }
  static void totals(Path output, String name, Map<String, long[]> data) throws Exception {
    try (var out = new PrintWriter(Files.newBufferedWriter(output.resolve(name)))) {
      row(out, "key", "events", "weight_bytes");
      for (var entry : data.entrySet()) row(out, entry.getKey(), entry.getValue()[0], entry.getValue()[1]);
    }
  }
  public static void main(String[] args) throws Exception {
    Path recording = Path.of(args[0]), output = Path.of(args[1]);
    Files.createDirectories(output);
    // A delayed recording's first allocation weight can include bytes allocated
    // before recording began. Locate the first timestamp per thread before
    // attributing weights; RecordingFile events need not be globally ordered.
    var firstAllocation = new HashMap<Long, Instant>();
    try (var file = new RecordingFile(recording)) {
      while (file.hasMoreEvents()) {
        var e = file.readEvent();
        if (e.getEventType().getName().equals("jdk.ObjectAllocationSample")) {
          long id = Objects.requireNonNull(e.getThread()).getJavaThreadId();
          firstAllocation.merge(id, e.getStartTime(), (a,b) -> a.isBefore(b) ? a : b);
        }
      }
    }
    var allocationClasses = new TreeMap<String, long[]>();
    var allocationCategories = new TreeMap<String, long[]>();
    var allocationSites = new TreeMap<String, long[]>();
    var allocationProjectStacks = new TreeMap<String, long[]>();
    var executionCategories = new TreeMap<String, long[]>();
    var executionSites = new TreeMap<String, long[]>();
    var executionProjectStacks = new TreeMap<String, long[]>();
    var executionThreads = new TreeMap<String, long[]>();
    long allocationEvents = 0, executionEvents = 0, allocationTruncated = 0, executionTruncated = 0;
    try (var file = new RecordingFile(recording);
         var boundaries = new PrintWriter(Files.newBufferedWriter(output.resolve("excluded-allocation-boundaries.csv")));
         var counts = new PrintWriter(Files.newBufferedWriter(output.resolve("class-counts.csv")));
         var collections = new PrintWriter(Files.newBufferedWriter(output.resolve("collections.csv")))) {
      row(counts, "gc_id", "time", "class", "count", "bytes");
      row(boundaries, "thread_id", "thread_name", "time", "class", "weight_bytes");
      row(collections, "gc_id", "time", "cause", "name", "duration_ns");
      while (file.hasMoreEvents()) {
        var e = file.readEvent();
        switch (e.getEventType().getName()) {
          case "jdk.ExecutionSample" -> {
            var thread = e.getThread("sampledThread");
            if (thread == null) continue;
            add(executionThreads, thread.getJavaThreadId() + ":" + thread.getJavaName(), 0);
            // ScalaTest can temporarily rename the calling thread. These fresh
            // HotSpot command-line JVMs run the benchmark on Java thread 1.
            if (thread.getJavaThreadId() != 1) continue;
            var frames = frames(e);
            executionEvents++;
            if (e.getStackTrace() != null && e.getStackTrace().isTruncated()) executionTruncated++;
            add(executionCategories, category(frames), 0);
            add(executionSites, frames.isEmpty() ? "<no stack>" : frames.getFirst(), 0);
            add(executionProjectStacks, String.join(" <- ", frames.stream().filter(s -> s.startsWith("hkmc2.")).limit(6).toList()), 0);
          }
          case "jdk.ObjectAllocationSample" -> {
            var thread = Objects.requireNonNull(e.getThread());
            if (e.getStartTime().equals(firstAllocation.get(thread.getJavaThreadId()))) {
              row(boundaries, thread.getJavaThreadId(), thread.getJavaName(), e.getStartTime(), normalized(e.getClass("objectClass").getName()), e.getLong("weight"));
              continue;
            }
            var frames = frames(e);
            long weight = e.getLong("weight");
            allocationEvents++;
            if (e.getStackTrace() != null && e.getStackTrace().isTruncated()) allocationTruncated++;
            add(allocationClasses, normalized(e.getClass("objectClass").getName()), weight);
            add(allocationCategories, category(frames), weight);
            add(allocationSites, frames.isEmpty() ? "<no stack>" : frames.getFirst(), weight);
            add(allocationProjectStacks, String.join(" <- ", frames.stream().filter(s -> s.startsWith("hkmc2.")).limit(6).toList()), weight);
          }
          case "jdk.ObjectCountAfterGC" -> row(counts, e.getInt("gcId"), e.getStartTime(), normalized(e.getClass("objectClass").getName()), e.getLong("count"), e.getLong("totalSize"));
          case "jdk.GarbageCollection" -> row(collections, e.getInt("gcId"), e.getStartTime(), e.getString("cause"), e.getString("name"), e.getDuration().toNanos());
        }
      }
    }
    totals(output,"allocation-classes.csv",allocationClasses);
    totals(output,"allocation-categories.csv",allocationCategories);
    totals(output,"allocation-sites.csv",allocationSites);
    totals(output,"allocation-project-stacks.csv",allocationProjectStacks);
    totals(output,"execution-categories.csv",executionCategories);
    totals(output,"execution-sites.csv",executionSites);
    totals(output,"execution-project-stacks.csv",executionProjectStacks);
    totals(output,"execution-threads.csv",executionThreads);
    try (var out = new PrintWriter(Files.newBufferedWriter(output.resolve("events.csv")))) {
      row(out,"kind","events","truncated_stacks");
      row(out,"allocation",allocationEvents,allocationTruncated);
      row(out,"execution_main_thread",executionEvents,executionTruncated);
    }
  }
}
