# Unicode-Aware Diagnostic Rendering (Asai Approach)

**Date:** 2026-05-08
**Status:** Design - Critical correction to Week 5 implementation
**Reference:** https://redprl.org/asai/asai/design.html

---

## ⚠️ CRITICAL: You CANNOT Align Carets with Code!

**The key insight from Asai:**

```
╭ ￭ /path/to/file.cool
┆ 1 | aaaaaaaaaa
┆ 2 | bbbbbbbbbb
╯   ^ when stepping into the abyss
```

**The `^` is NOT aligned with any character in the code!**

It's just placed at the left margin (after the line number). There is **NO calculation** of visual column positions. This is the only way to achieve Unicode correctness.

---

## The Problem: Visual Width is Ill-Defined

Our original Week 5 design planned to use `unicode-width` crate and column alignment for caret rendering. **This is fundamentally flawed.**

### Why Visual Width Doesn't Work

From Asai's design rationale:

1. **Emoji sequences** - 🏴‍☠️ (pirate flag) may render as 1 emoji OR as 2 (🏴 + ☠️) depending on platform
2. **East Asian Width "Ambiguous"** - Characters that have different widths on different terminals
3. **Grapheme clusters** - User-perceived characters don't match byte/character counts
4. **Variable-width fonts** - Some terminals use proportional fonts
5. **Bidirectional text** - Hebrew, Arabic (not yet supported, but column numbers would break it)

### Display Stability Levels

- **Level 0:** Assume all characters same width → **BROKEN on all platforms**
- **Level 1:** Use `wcwidth`/`unicode-width` heuristics → **Fails on emoji, CJK ambiguous chars** ← Our original plan
- **Level 2:** Minimal assumptions (Halfwidth/Fullwidth, box-drawing) → **Asai's choice** ← What we should do
- **Level 3:** No assumptions except grapheme equality → **Too restrictive** (can't show line numbers)

**Our original design was Level 1. We must move to Level 2.**

---

## The Solution: No Column Numbers, Byte-Oriented Rendering

### Core Principles (from Asai)

1. ✅ **Byte offsets as positions** - Our `Span` type is already correct!
2. ❌ **NO column numbers** - Never calculate or display column positions
3. ❌ **NO visual width calculations** - Don't use `wcwidth`, `unicode-width`, or any heuristics
4. ✅ **Exact byte extraction** - Use byte offsets to extract exact text from source
5. ✅ **Line-based highlighting** - Show whole lines, highlight ranges inline

### What This Means for Rendering

**NEVER do this:**
```
42 |     let foo = f x
   |         ^^^ variable name too ugly
```
This assumes `foo` starts at visual column 8, which is **undefined** for Unicode.

**INSTEAD do this (Option A - Inline):**
```
error[E0001]: variable name too ugly
  --> src/main.hwml:42:9-42:12
   |
42 |     let foo = f x
   |
   = the variable `foo` has an ugly name
```

**OR this (Option B - Separate display):**
```
error[E0001]: variable name too ugly
  --> src/main.hwml:42:9-42:12
   |
   in this expression:
       foo
   |
   = the variable `foo` has an ugly name
```

**OR this (Option C - Asai actual style):**
```
error[E0001]: variable name too ugly
╭ ￭ src/main.hwml
┆ 42 | let foo = f x
╯    ^ the variable `foo` has an ugly name
```
(The `^` is **NOT aligned** with `foo`! It's just at the left margin after the line number. No visual column calculation!)

---

## Updated Implementation Plan for Week 5

### Remove These Tasks:
- ❌ "Implement Unicode-aware column alignment"
- ❌ "Use unicode-width crate to calculate display width"
- ❌ "Handle tabs (expand to 4 spaces), grapheme clusters"

### Add These Tasks:
- ✅ Implement byte-offset extraction (use `Span` to slice source text)
- ✅ Implement line-based rendering (show whole lines from source)
- ✅ Implement inline highlighting (display extracted text separately)
- ✅ Use ANSI color for ranges (no caret alignment needed)
- ✅ Test with emoji, CJK, RTL text (verify Level 2 stability)

### Rendering Algorithm (Actual Asai Style)

**Key insight:** The `^` marker is **NOT aligned** with the code. It's just a left-margin indicator!

```rust
fn render_diagnostic(diag: &Diagnostic, source: &str) -> String {
    let mut output = String::new();

    // 1. Header with box-drawing
    output.push_str(&format!("￫ {}[{}]: {}\n",
        severity_name(diag.severity),
        diag.code.as_ref().map(|c| c.as_str()).unwrap_or(""),
        diag.message
    ));

    // 2. Start block with file path
    output.push_str(&format!("╭ ￭ {}\n", file_path));

    // 3. Source context - show whole line(s)
    let lines = get_lines_for_span(source, diag.span);
    for (line_num, line_text) in lines {
        output.push_str(&format!("┆ {} | {}\n", line_num, line_text));
    }

    // 4. End block with message (NO CARET ALIGNMENT!)
    // The ^ is just at the left margin, NOT aligned with the code
    output.push_str(&format!("╯    ^ {}\n",
        diag.explanation.as_deref().unwrap_or(diag.message)
    ));

    output
}
```

**What makes this work:**
- Box-drawing characters (╭ ┆ ╯) create visual structure
- The `^` is always at the same position (left margin)
- NO calculation of where the error is in the line
- Works with ANY Unicode content in the source code

---

## Key Differences from Original Design

| Original (Wrong) | Corrected (Asai) |
|------------------|------------------|
| Calculate visual width with `unicode-width` | Never calculate visual width |
| Align `^^^` carets under text | Show whole lines or inline text |
| Column numbers in locations | Byte offsets in locations |
| Level 1 stability | Level 2 stability |
| Breaks on emoji 🏴‍☠️ | Works with any Unicode |

---

## Dependencies Update

### Remove:
```toml
unicode-width = "0.1"  # DON'T USE - violates Asai principles
```

### Keep:
```toml
termcolor = "1.4"  # For ANSI color escapes - fine to use
```

---

## Testing Requirements

Week 5 tests MUST verify:

1. ✅ Emoji sequences render correctly (🏴‍☠️, 🏳️‍🌈, 👨‍👩‍👧‍👦)
2. ✅ CJK characters don't break layout (全角文字)
3. ✅ Mixed-width text works (ASCII + CJK + emoji)
4. ✅ No assumptions about visual column positions
5. ✅ Byte offsets correctly extract spans

---

## References

- Asai design rationale: https://redprl.org/asai/asai/design.html
- Unicode Emoji sequences: https://unicode.org/reports/tr51/
- East Asian Width: https://unicode.org/reports/tr11/
- Why byte offsets: https://github.com/redprl/asai#raw-bytes-as-positions
