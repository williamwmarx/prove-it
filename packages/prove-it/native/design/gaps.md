# The native engine's gaps

What the native engine now does where it declined or stopped, as built: one section per change,
newest last. DESIGN.md holds the plan; this file holds how each gap was closed.

## ToString

- **ToString** (`compile/builtins.rs`) gives TLC's text of its argument (`tla_values::print`,
  `formatValue(v, true)`), and ranks the string it makes, as `rankString` does. It stops where
  the text depends on how TLC built the value, which the store forgets (`is_printable`), as Print
  and PrintT do.
- **The search never orders the strings it ranks.** TLC ranks a string as it makes it, and the
  engine may make ToString's strings in another order: across successors it pipelines, where it
  builds every entry of a function TLC applies lazily, or for a text `\o` made earlier, which
  the store keeps unranked. So the store freezes TLC's order when the search starts
  (`freeze_string_order`), and comparing a string ranked since with another string stops the
  search. A search that ranked strings hands over none of its states, so the interpreter makes
  them again from the start, in TLC's order. Starting over would print again what the search
  printed, so a model that prints and uses ToString declines.
- With it, the native engine declines no corpus model the TypeScript engine searches:
  simple_strings and UnicodeStringDiskStateQueue, the two it declined for ToString, now search in
  Rust until the stop the TypeScript engine reaches. The other 49 it declines (TLC under 20 s) the
  TypeScript engine refuses too, for the same reason.

---
