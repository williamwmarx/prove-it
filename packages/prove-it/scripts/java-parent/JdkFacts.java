// Development-only metadata extraction for scripts/java-parent.ts. Not used by the native
// executable. `packages` prints each system module of the running JDK and, below it, one
// `module<TAB>package` line for each package it holds; `entries <zip>` prints the name of every
// entry of a zip, duplicates included; `read <zip> <entry>` writes an entry's bytes.
import java.io.IOException;
import java.lang.module.ModuleFinder;
import java.util.zip.ZipFile;

class JdkFacts {
    public static void main(String[] args) throws IOException {
        switch (args[0]) {
            case "packages" -> ModuleFinder.ofSystem().findAll().stream()
                .sorted((a, b) -> a.descriptor().name().compareTo(b.descriptor().name()))
                .forEach(reference -> {
                    var descriptor = reference.descriptor();
                    System.out.println(descriptor.name());
                    descriptor.packages().stream().sorted()
                        .forEach(name -> System.out.println(descriptor.name() + "\t" + name));
                });
            case "entries" -> {
                try (var zip = new ZipFile(args[1])) {
                    zip.stream().forEach(entry -> System.out.println(entry.getName()));
                }
            }
            case "read" -> {
                try (var zip = new ZipFile(args[1])) {
                    var entry = zip.getEntry(args[2]);
                    if (entry == null) throw new IOException("no entry " + args[2]);
                    try (var input = zip.getInputStream(entry)) {
                        input.transferTo(System.out);
                    }
                }
                System.out.flush();
            }
            default -> throw new IllegalArgumentException(args[0]);
        }
    }
}
