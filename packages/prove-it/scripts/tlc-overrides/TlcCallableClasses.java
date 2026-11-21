import java.lang.reflect.*;
import java.util.*;
import java.util.jar.*;
import tlc2.overrides.*;

// Writes the rows of native/crates/tla-front/src/tlc_callable_classes.tsv: for each operator a
// Java method of the pinned jar overrides, the module, the operator, the Java value class TLC
// builds for it (Method, EagerValue or Evaluating), its minimum level, the declaring class, the
// method, its arity and how TLC installed it. Legacy class methods are considered first; only the
// actual packaged ITLCOverrides provider list contributes annotated replacements. Multiple
// distinct final providers for one receiver are explicitly Unknown.
//
// With the jar of TLC at d8fb231 (its SHA-256 is tlc.jar_sha256 in
// native/crates/tla-front/src/java_parent/provenance.json) and JDK 21:
// javac -cp tla2tools.jar TlcCallableClasses.java && java -cp tla2tools.jar:. TlcCallableClasses tla2tools.jar
// The rows go to standard output, after the table's header. The header records the SHA-256 of
// this file and of the rows, which tla-front's test
// `callable_classes_record_the_hashes_of_their_generator_and_rows` checks.
public final class TlcCallableClasses {
  static final Map<String, Set<String>> selected = new TreeMap<>();
  static final Set<String> annotated = new HashSet<>();
  static void record(String module, String operator, String kind, int level, Method m, String event) {
    String key = module + "\t" + operator;
    if (!event.equals("Legacy") && annotated.add(key)) selected.remove(key);
    if (kind.equals("Method") && m.getParameterCount() == 0 && Modifier.isFinal(m.getModifiers())) kind = "EagerValue";
    String descriptor = kind + "\t" + level + "\t" + m.getDeclaringClass().getName() + "\t" + m.getName() + "\t" + m.getParameterCount() + "\t" + event;
    selected.computeIfAbsent(key, k -> new TreeSet<>()).add(descriptor);
  }
  public static void main(String[] args) throws Exception {
    List<Class<?>> classes = new ArrayList<>();
    try (JarFile jar = new JarFile(args[0])) {
      for (Enumeration<JarEntry> e = jar.entries(); e.hasMoreElements();) {
        String n = e.nextElement().getName();
        if (n.startsWith("tlc2/module/") && n.endsWith(".class") && !n.contains("$"))
          classes.add(Class.forName(n.replace('/', '.').replace(".class", ""), true, TlcCallableClasses.class.getClassLoader()));
      }
    }
    Method mapName = Class.forName("tlc2.tool.impl.TLARegistry").getMethod("mapName", String.class);
    for (Class<?> c : classes) {
      for (Method m : c.getDeclaredMethods()) {
        int mod = m.getModifiers();
        if (!Modifier.isPublic(mod) || !Modifier.isStatic(mod)) continue;
        if (m.getAnnotation(TLAPlusOperator.class) == null && m.getAnnotation(Evaluation.class) == null)
          record(c.getSimpleName(), (String)mapName.invoke(null, m.getName()), "Method", 0, m, "Legacy");
      }
    }
    ITLCOverrides index = (ITLCOverrides)Class.forName("tlc2.module.TLCBuiltInOverrides").getConstructor().newInstance();
    for (Class<?> c : index.get()) {
      for (Method m : c.getDeclaredMethods()) {
        int mod = m.getModifiers();
        if (!Modifier.isPublic(mod) || !Modifier.isStatic(mod)) continue;
        TLAPlusOperator op = m.getAnnotation(TLAPlusOperator.class);
        Evaluation ev = m.getAnnotation(Evaluation.class);
        if (ev != null) record(ev.module(), ev.definition(), "Evaluating", ev.minLevel(), m, "Evaluation");
        else if (op != null) record(op.module(), op.identifier(), "Method", op.minLevel(), m, "Annotated");
      }
    }
    for (Map.Entry<String, Set<String>> e : selected.entrySet()) {
      if (e.getValue().size() == 1) System.out.println(e.getKey() + "\t" + e.getValue().iterator().next());
      else {
        System.out.println(e.getKey() + "\tUnknown\t0\tambiguous\tambiguous\t0\tUnknown");
        System.err.println("Unknown ambiguous constructor: " + e.getKey() + " " + e.getValue());
      }
    }
  }
}
