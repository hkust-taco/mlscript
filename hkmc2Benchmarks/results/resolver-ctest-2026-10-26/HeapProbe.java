import java.lang.management.*;
import java.lang.ref.Reference;
import java.util.*;

public class HeapProbe {
  // Make transient allocations observable without keeping their whole history.
  static volatile Object garbage;
  static List<MemoryPoolMXBean> pools = ManagementFactory.getMemoryPoolMXBeans().stream().filter(p -> p.getType() == MemoryType.HEAP).toList();
  static MemoryMXBean memory = ManagementFactory.getMemoryMXBean();
  static void reading(String label) {
    System.gc();
    // Snapshots exclude allocation buffers reserved while polling current usage.
    long snapshot = 0;
    for (var pool : pools) {
      var usage = pool.getCollectionUsage();
      if (usage == null) throw new IllegalStateException(pool.getName());
      snapshot += usage.getUsed();
    }
    long polled = memory.getHeapMemoryUsage().getUsed();
    System.out.println(label + "," + snapshot + "," + polled);
  }
  static void held() {
    var root = new ArrayList<byte[]>();
    for (int i=0;i<200000;i++) root.add(new byte[256]);
    for (int i=0;i<1000000;i++) garbage = new byte[4096];
    for (int i=0;i<4;i++) reading("held-"+i);
    Reference.reachabilityFence(root);
  }
  public static void main(String[] args) {
    System.out.println("phase,collection_snapshot_bytes,current_heap_bytes");
    held();
    for (int i=0;i<8;i++) reading("released-"+i);
  }
}
