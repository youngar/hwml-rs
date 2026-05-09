# ADR-016: No Column Alignment in Diagnostic Rendering

**Status:** Approved  
**Date:** 2026-05-08  
**Phase:** Diagnostic Framework (Week 5)  
**Confidence:** 0.99  
**Deciders:** Architecture Team (after studying Asai source code)  
**Context Tags:** #diagnostics #unicode #terminal-rendering #asai
**Reference:** `external/asai/`, `design/UNICODE-RENDERING-ASAI-APPROACH.md`

---

## Context

HWML needs to render diagnostic messages in terminals with source code snippets. A common approach is to use "caret alignment" where `^` characters are positioned under highlighted code:

```
42 | let foo = true
   |     ^^^ expected Nat, found Bool
```

This requires calculating the **visual column position** of each character.

### The Problem

Visual width is **fundamentally ill-defined** for Unicode:

1. **Emoji sequences** - 🏴‍☠️ (pirate flag) renders as 1 emoji OR 2 (🏴 + ☠️) depending on platform
2. **East Asian Width "Ambiguous"** - Characters with different widths on different terminals  
3. **Combining characters** - é vs. é (one codepoint vs. e + ◌́)
4. **Variable-width fonts** - Some terminals use proportional fonts
5. **Bidirectional text** - Hebrew, Arabic (not yet supported)

Libraries like `unicode-width` and `wcwidth` are **heuristics** that only work for common cases. They fail on:
- Emoji sequences (ZWJ, variation selectors)
- Ambiguous-width CJK characters
- Font-specific rendering decisions
- Terminal-specific behavior

### Requirements

- Support arbitrary Unicode in user code (emoji, CJK, combining characters)
- Work across all terminals (Linux, macOS, Windows)
- Work with variable-width fonts
- No visual glitches or misalignment

---

## Alternatives Considered

### Option 1: Column Alignment with `unicode-width` (Rejected)

Use `unicode-width` crate to calculate visual column positions.

**Pros:**
- Works for ASCII and simple Unicode
- Familiar pattern from other compilers

**Cons:**
- ❌ Breaks on emoji sequences (🏴‍☠️, 🏳️‍🌈, 👨‍👩‍👧‍👦)
- ❌ Wrong for East Asian Width "Ambiguous" characters
- ❌ Terminal-dependent (same code, different rendering)
- ❌ Font-dependent (monospace vs. duospaced)
- ❌ Only achieves "Level 1" display stability (Asai taxonomy)

**Example of failure:**
```
42 | let 変数 = 🏴‍☠️
   |     ^^   ^      ← Wrong! CJK is 2 cells, emoji is 1-2 depending on terminal
```

**Verdict:** **Rejected** - Fundamentally unsound, will produce visual glitches

### Option 2: Column Alignment with Exact Font Metrics (Rejected)

Query the terminal for font metrics and calculate exact visual positions.

**Pros:**
- Theoretically correct for a given terminal

**Cons:**
- ❌ Not possible in practice (terminals don't expose font metrics)
- ❌ Different terminals have different fonts
- ❌ Users can change fonts
- ❌ SSH sessions have unknown remote terminal

**Verdict:** **Rejected** - Not implementable

### Option 3: ANSI Underline + Fixed-Position Marker (Chosen - Asai Approach)

Use ANSI escape codes to **underline** highlighted text in-place. Put `^` marker at a **fixed left margin**.

**Pros:**
- ✅ Works with ANY Unicode (emoji, CJK, RTL, combining characters)
- ✅ Terminal-independent (ANSI underline is standard)
- ✅ Font-independent (underline follows actual character positions)
- ✅ No visual width calculation needed
- ✅ Achieves "Level 2" display stability (Asai taxonomy)
- ✅ Proven approach (used by Asai, OCaml compiler framework)

**Cons:**
- Requires ANSI escape code support (standard on all modern terminals)
- `^` is not aligned with code (acceptable - it's just a marker)

**Example:**
```
 ￫ error[E0308]
 ￭ main.hwml
 42 | let foo = true      ← underlined using \x1b[4m escape
    ^ expected Nat       ← marker at fixed position
```

**Verdict:** **Best option** - Only correct approach for Unicode

---

## Decision

**Use ANSI underline escapes (`\x1b[4m`) to highlight ranges within source text. Place `^` marker at a fixed left margin position.**

### Implementation

```rust
fn render_diagnostic(diag: &Diagnostic, source: &str) -> String {
    let mut output = String::new();
    
    // Header
    output.push_str(&format!("￫ error[{}]\n", diag.code));
    output.push_str(&format!("￭ {}\n", file_path));
    
    // Source line with ANSI underline
    let line_text = get_line(source, diag.span);
    let (before, highlighted, after) = split_by_span(line_text, diag.span);
    
    output.push_str(&format!("{} | {}", line_num, before));
    output.push_str("\x1b[4m");  // Start underline
    output.push_str(highlighted);
    output.push_str("\x1b[m");   // Reset
    output.push_str(after);
    output.push_str("\n");
    
    // Marker at FIXED position (no alignment!)
    output.push_str("   ^ ");
    output.push_str(&diag.message);
    
    output
}
```

### Key Principle

**Never calculate visual column positions.** The terminal knows how to render text - trust it!

---

## Rationale

### Why This Works

1. **ANSI underline (`\x1b[4m`) is visual**
   - Terminal places underline under actual rendered characters
   - Works regardless of character width
   - Automatically handles emoji, CJK, combining characters

2. **Fixed-position `^` is acceptable**
   - It's just a marker saying "the underlined part is the error"
   - Users don't need exact alignment - the underline shows location
   - Asai proves this works well in practice

3. **No heuristics needed**
   - We extract the exact bytes from the span
   - Terminal renders them with underline
   - No width calculation, no guessing

### Asai Evidence

Asai (used by RedPRL, cooltt, and other proof assistants) uses this exact approach. From `external/asai/test/Test_tty.expected`:

```
￫ error[hello]
￭ /path/to/file.cool
1 | aaa[4maaaaaaa[m        ← [4m = underline start, [m = reset
2 | [4mbbbbbbbbbb[m
3 | [4mcccc[mcccccc
  ^                      ← Fixed position, never aligned!
```

This has been **battle-tested** in production theorem provers with complex Unicode content.

---

## Consequences

### Positive

✅ **Flawless Unicode support** - Works with any valid Unicode in source code
✅ **No `unicode-width` dependency** - Simpler, more reliable
✅ **Terminal-independent** - Same rendering across Linux/macOS/Windows
✅ **Font-independent** - Works with any font (monospace, duospaced, proportional)
✅ **Future-proof** - Supports bidirectional text when we add it
✅ **Proven approach** - Asai validates this works in practice

### Negative

⚠️ **Requires ANSI support** - Won't work on very old terminals (acceptable)
⚠️ **`^` not aligned** - Marker is at fixed position, not under code (acceptable - underline shows location)

### Neutral

- Box-drawing characters (`╭` `┆` `╯`) provide visual structure
- Colors use ANSI codes (already standard for compiler output)

---

## Related Decisions

- **ADR-014:** Byte-Level Location Tracking - Why we use byte offsets as positions
- **ADR-013:** UTF-8 Internal Representation - Why strings are UTF-8

---

## References

- **Asai Design:** https://redprl.org/asai/asai/design.html#no-column-numbers-%28but-still-with-highlighting%29
- **Asai Source:** `external/asai/src/tty/Tty.ml`
- **Display Stability Levels:** See `design/UNICODE-RENDERING-ASAI-APPROACH.md`
- **Unicode Emoji:** https://unicode.org/reports/tr51/
- **East Asian Width:** https://unicode.org/reports/tr11/

---

## Notes

**Key Lesson:** Documentation often describes principles abstractly. Studying **source code** revealed that Asai uses ANSI underlines, not column alignment. This is a critical implementation detail not obvious from the design document alone.

**For Implementers:** See `design/UNICODE-RENDERING-ASAI-APPROACH.md` for detailed rendering algorithms and test requirements.
