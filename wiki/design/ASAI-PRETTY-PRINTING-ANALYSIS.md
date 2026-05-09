# Asai Pretty Printing and Document Formatting

**Date:** 2026-05-08  
**Status:** Research Complete  
**Related:** `UNICODE-RENDERING-ASAI-APPROACH.md`, `ADR-016`

---

## Overview

Asai uses OCaml's `Format` module for structured pretty printing rather than pre-formatted strings. This enables:
- **Automatic line breaking** and reflow based on terminal width
- **No manual column calculations** - the formatter handles layout
- **Composable text fragments** using format strings
- **Separation of content from presentation**

---

## Core Concept: Text as Function

```ocaml
(* Text is a function that takes a formatter and renders to it *)
type t = Format.formatter -> unit
```

**Key Rule:** Text must NOT contain literal control characters (including `\n`). Instead:
- Use format directives: `@,` (break hint), `@ ` (space break), `@.` (force newline)
- Convert pre-formatted strings with `Text.make` which converts `\n` to `Format.pp_force_newline`

**Benefits:**
- Layout engine controls wrapping and indentation
- Can render to different widths without recalculation
- Composes naturally: `textf "@[<2>prefix:@ @[%t@]@]" inner_text`

---

## Terminal Rendering Architecture

### 1. **ANSI Escape Code Usage**

```ocaml
(* From Test_tty.expected - actual output *)
[33mwarning[hello][m           (* Yellow warning *)
[31merror[bye][m               (* Red error *)
[41;30mbug[hello][m            (* Red background, black text for Bug *)
[4;31mhighlighted[m           (* Red + underline *)
[2m^[m                        (* Dim/faint *)
```

**ANSI Codes Used:**
- `[4m` - Underline (for highlighting ranges)
- `[31m` - Red (Error)
- `[33m` - Yellow (Warning)
- `[32m` - Green (Info)
- `[34m` - Blue (Hint)
- `[41;30m` - Red background + black foreground (Bug)
- `[2m` - Dim/faint (for fringe decorations)
- `[1m` - Bold (when colors disabled but ANSI enabled)
- `[m` - Reset

**Three Rendering Modes:**
1. **`Enabled_with_color`** - Full ANSI colors + underline
2. **`Enabled_without_color`** - Bold/underline only (NO_COLOR env var)
3. **`Disabled`** - Use `«` and `»` markers instead of underline

---

### 2. **Source Marker System**

Asai builds a **marked source representation** that separates:
- **Tokens:** Strings and marks (range delimiters)
- **Lines:** Sequences of tokens with attached messages
- **Blocks:** Groups of consecutive highlighted lines
- **Parts:** Blocks from the same file

```ocaml
type 'tag token =
  | String of string
  | Mark of special_position option * 'tag mark

type 'tag mark =
  | Range_begin of 'tag
  | Range_end of 'tag
  | Point of 'tag

type 'tag line = {
  marks : 'tag list;      (* Messages attached to this line *)
  tokens : 'tag token list
}
```

**Rendering Process:**
1. Take ranges (byte offsets) + tags
2. Read source from files
3. Split into lines (handling Unicode line breaks)
4. Insert marks at byte positions
5. Build block structure (splitting when too many non-highlighted lines)
6. Render with ANSI underlines or angle quotation marks

---

### 3. **Block Splitting**

**Parameter:** `block_splitting_threshold` (default: 5)

If more than N consecutive non-highlighted lines appear, split into separate blocks:

```
 ￫ warning[hello]
 ╭ ￭ /path/to/file.cool
 ┆ 1 | a[underline]aaaaaaaaa
 ┆ 2 | bbbbbbbbbb
 ┆ 3 | cccc[/underline]cccccc
 ╯   ^ when stepping into the abyss
 ￭ /path/to/file.cool      ← New block
 1 | aaa[underline]aaaaaaa
 2 | bbbbbbbbbb
 3 | cccc[/underline]cccccc
   ^ hello from here
```

**Box-drawing characters:**
- `╭` - Top of multi-line backtrace/remark block
- `┆` - Middle of block  
- `╯` - Bottom of block
- `ꭍ` - Single-line backtrace/remark

---

### 4. **No Column Alignment**

**Critical:** The `^` marker is ALWAYS at a **fixed left margin position**.

```
 [2m1 |[m aaa[4;31maaaaaaa[m
 [2m2 |[m [4;31mbbbbbbbbbb[m
 [2m3 |[m [4;31mcccc[mcccccc
   [2m^[m [31mthis is an error[m    ← Fixed indent, not aligned with code
```

The underline `[4m...[m` shows **what** is highlighted.  
The `^` shows **that there's a message**, not where it starts.

---

## Format Module Integration

Asai uses OCaml's `Format` module extensively:

```ocaml
(* Rendering source line *)
Format.fprintf fmt (" " ^^ highlight "%*d |" ^^ " ")
  (Ansi.style_string ~param:param.ansi Tty_style.fringe)
  param.line_number_width line_num
  (Ansi.reset_string ~param:param.ansi Tty_style.fringe);

(* Highlighted segment *)
Format.fprintf fmt (highlight "%s")
  (Ansi.style_string ~param:param.ansi style)
  (String_utils.replace_control ~tab_size:param.tab_size segment)
  (Ansi.reset_string ~param:param.ansi style)
```

**Format Directives:**
- `%*d` - Right-align integer with dynamic width
- `%s` - String
- `%t` - Embedded text (formatter function)
- `@.` - Force newline
- `@[...]@]` - Box for grouping
- `@<n>%s` - Literal string of width n (for ANSI escapes that don't take space)

---

## Text Conversion

```ocaml
(* Convert string with newlines to pretty-printed text *)
let make s fmt =
  Format.(pp_print_list ~pp_sep:pp_force_newline pp_print_string) fmt @@
  String.split_on_char '\n' s

(* Create formatted text *)
let makef = Format.dprintf  (* Delayed printf - returns formatter fn *)

(* Flatten to string for LSP *)
let to_string text : string =
  let buf = Buffer.create 20 in
  let fmt = Format.formatter_of_buffer buf in
  Format.pp_set_geometry fmt ~max_indent:2 ~margin:(Format.pp_infinity-1);
  text fmt;
  Format.pp_print_flush fmt ();
  Str.global_replace (Str.regexp "\\([\r\n]+ *\\)+") " " @@
  Buffer.contents buf
```

---

## Implications for HWML

### 1. **Use a Pretty-Printing Library**

Rust options:
- **`pretty`** crate - Wadler-Lindig pretty printer (similar to OCaml's Format)
- **`prettyplease`** - Syn-based Rust formatter library
- Manual `std::fmt` with careful formatting

**Recommendation:** Start simple with `std::fmt`, add `pretty` crate later if needed.

### 2. **Text Type**

```rust
/// Text that can be pretty-printed
pub struct Text {
    /// Formatted string segments
    segments: Vec<TextSegment>,
}

enum TextSegment {
    Literal(String),
    Newline,
    Indent(Box<Text>),
}

impl Text {
    pub fn from_str(s: &str) -> Self {
        // Split on \n, convert to segments
    }
    
    pub fn to_string(&self) -> String {
        // Flatten for LSP
    }
    
    pub fn fmt(&self, f: &mut fmt::Formatter, width: usize) -> fmt::Result {
        // Render with line breaking
    }
}
```

### 3. **Keep Asai's Loctext Pattern**

```rust
pub struct Loctext {
    pub loc: Option<Span>,
    pub text: Text,  // Use Text instead of String
}
```

---

## Summary

**Asai's Key Innovations:**
1. ✅ **Text as formatter functions** - Composable, width-independent
2. ✅ **ANSI underlines** - No column alignment needed
3. ✅ **Block splitting** - Smart multi-range display
4. ✅ **Marked source** - Structured representation before rendering
5. ✅ **Three output modes** - Color, monochrome-ANSI, plain

**For HWML Week 5:**
- Start with simple string-based rendering
- Use ANSI underlines (not caret alignment)
- Implement block splitting
- Consider adding `pretty` crate for advanced layouts later

**References:**
- `external/asai/src/Text.ml` - Text abstraction
- `external/asai/src/tty/Tty.ml` - Terminal rendering
- `external/asai/src/Marked_source_data.ml` - Marked source structure
