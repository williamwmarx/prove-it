import java.lang.reflect.*;
import java.util.*;
import java.util.jar.*;
import tlc2.overrides.*;

// Writes TLC's Java overrides of TLA+ operators, which native/crates/tla-front/src/tlc_overrides.tsv
// holds: the module, the operator and its level (`minLevel`), one per line, sorted. They are the
// public static methods of the classes TLC loads for a module (`processModuleOverrides`): those of
// tlc2/module, named after the module, by `TLARegistry.mapName` of the method's name, and those
// `@TLAPlusOperator` or `@Evaluation` names, CommunityModules' in tlc2/overrides among them.
//
// javac -cp tla2tools.jar TlcOverrides.java && java -cp tla2tools.jar:. TlcOverrides tla2tools.jar
public class TlcOverrides {
  public static void main(String[] args) throws Exception {
    TreeSet<String> out = new TreeSet<>();
    List<Class<?>> classes = new ArrayList<>();
    try (JarFile jar = new JarFile(args[0])) {
      for (Enumeration<JarEntry> e = jar.entries(); e.hasMoreElements();) {
        String n = e.nextElement().getName();
        if ((n.startsWith("tlc2/module/") || n.startsWith("tlc2/overrides/")) && n.endsWith(".class") && !n.contains("$")) {
          classes.add(Class.forName(n.replace('/', '.').replace(".class", ""), false, TlcOverrides.class.getClassLoader()));
        }
      }
    }
    Method mapName = Class.forName("tlc2.tool.impl.TLARegistry").getMethod("mapName", String.class);
    for (Class<?> c : classes) {
      boolean isModuleClass = c.getName().startsWith("tlc2.module.");
      for (Method m : c.getDeclaredMethods()) {
        int mod = m.getModifiers();
        if (!Modifier.isPublic(mod) || !Modifier.isStatic(mod)) continue;
        TLAPlusOperator op = m.getAnnotation(TLAPlusOperator.class);
        Evaluation ev = m.getAnnotation(Evaluation.class);
        if (op != null) out.add(op.module() + "\t" + op.identifier() + "\t" + op.minLevel());
        else if (ev != null) out.add(ev.module() + "\t" + ev.definition() + "\t" + ev.minLevel());
        else if (isModuleClass) out.add(c.getSimpleName() + "\t" + mapName.invoke(null, m.getName()) + "\t0");
      }
    }
    for (String line : out) System.out.println(line);
  }
}
