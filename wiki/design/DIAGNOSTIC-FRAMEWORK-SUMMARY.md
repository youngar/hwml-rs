# Diagnostic Framework - Quick Reference

**Date:** 2026-05-08  
**Status:** Navigation Hub  
**Purpose:** Quick reference for all diagnostic framework documentation

---

## 📚 Document Map

### Primary Documents (Start Here)

1. **`DIAGNOSTIC-IMPLEMENTATION-PLAN-REVISED.md`** ⭐ **ACTIVE PLAN**
   - Complete 6-week implementation plan
   - Based on Asai source code analysis
   - Type designs, architecture, week-by-week tasks
   - **Use this for:** Current implementation work

2. **`UNICODE-RENDERING-ASAI-APPROACH.md`** ⚠️ **CRITICAL**
   - Why column alignment is impossible
   - How Asai achieves flawless Unicode rendering
   - ANSI underline technique
   - **Use this for:** Understanding rendering approach

### Supporting Documents

3. **`DIAGNOSTIC-VFS-LSP-INTEGRATION.md`** 🔄 **SUPERSEDED**
   - Original 6-week plan (before Asai study)
   - Still useful for: Salsa integration details
   - **Status:** Marked superseded, kept for reference

### Research Foundation

4. **`research/diagnostic-framework-design.md`**
   - Theoretical foundation from Asai documentation
   - Design principles and patterns
   - **Use this for:** Understanding "why"

5. **`research/diagnostic-post-processing.md`**
   - Post-processing algorithms
   - Deduplication, pattern detection
   - **Use this for:** Week 4 implementation

6. **`research/asai-detailed-review.md`**
   - Detailed review of Asai design doc
   - **Use this for:** Deep dive into principles

### Related ADRs

7. **`decisions/ADR-014-byte-level-location-tracking.md`**
   - Why we use byte offsets (not line:column)
   - **Use this for:** Understanding position representation

---

## 🎯 Quick Answers

**"How do I implement terminal rendering?"**
→ `UNICODE-RENDERING-ASAI-APPROACH.md` + Week 5 in revised plan

**"What types should I use?"**
→ `DIAGNOSTIC-IMPLEMENTATION-PLAN-REVISED.md` Section "Revised Type Design"

**"How does Salsa integration work?"**
→ `DIAGNOSTIC-VFS-LSP-INTEGRATION.md` Section 1-2 (still valid!)

**"Why no column numbers?"**
→ `UNICODE-RENDERING-ASAI-APPROACH.md` Section "The Problem"

**"What's the implementation timeline?"**
→ `DIAGNOSTIC-IMPLEMENTATION-PLAN-REVISED.md` Weeks 1-6

**"Where's the Asai source code?"**
→ `external/asai/` in our repository

---

## 📊 Current Status (Week 1)

✅ **Completed:**
- Basic `hwml-diagnostic` crate created
- Initial types defined (Span, Severity, DiagnosticCode)
- Builder API implemented
- Unit tests passing

🔄 **Needs Revision:**
- Add `DiagnosticSeverity::Bug` level
- Redesign `Span` to include `Position` with line caching
- Separate backtrace from extra remarks
- Update builder for new structure

📋 **Next:** Week 2 Salsa Integration

---

## 🔗 External References

- **Asai Library:** https://github.com/RedPRL/asai
- **Asai Docs:** https://ocaml.org/p/asai/latest/doc/
- **Asai Design:** https://redprl.org/asai/asai/design.html
- **Our Clone:** `external/asai/` directory

---

## 📝 Notes

**Why Two Plans?**
- Original plan was based on Asai documentation
- Studying source code revealed critical implementation details
- Kept original for Salsa/VFS integration (still correct)
- Revised plan incorporates source code findings

**Key Lesson:**
Documentation describes principles, source code reveals implementation. Always study both!

---

**Last Updated:** 2026-05-08  
**Maintained by:** LLM (auto-updated with changes)
