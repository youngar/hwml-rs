# LLM Wiki

A pattern for building personal knowledge bases using LLMs.

This is an idea file, it is designed to be copy pasted to your own LLM Agent (e.g. OpenAI Codex, Claude Code, OpenCode / Pi, or etc.). Its goal is to communicate the high level idea, but your agent will build out the specifics in collaboration with you.

## The core idea

Most people's experience with LLMs and documents looks like RAG: you upload a collection of files, the LLM retrieves relevant chunks at query time, and generates an answer. This works, but the LLM is rediscovering knowledge from scratch on every question. There's no accumulation. Ask a subtle question that requires synthesizing five documents, and the LLM has to find and piece together the relevant fragments every time. Nothing is built up. NotebookLM, ChatGPT file uploads, and most RAG systems work this way.

The idea here is different. Instead of just retrieving from raw documents at query time, the LLM **incrementally builds and maintains a persistent wiki** — a structured, interlinked collection of markdown files that sits between you and the raw sources. When you add a new source, the LLM doesn't just index it for later retrieval. It reads it, extracts the key information, and integrates it into the existing wiki — updating entity pages, revising topic summaries, noting where new data contradicts old claims, strengthening or challenging the evolving synthesis. The knowledge is compiled once and then *kept current*, not re-derived on every query.

This is the key difference: **the wiki is a persistent, compounding artifact.** The cross-references are already there. The contradictions have already been flagged. The synthesis already reflects everything you've read. The wiki keeps getting richer with every source you add and every question you ask.

You never (or rarely) write the wiki yourself — the LLM writes and maintains all of it. You're in charge of sourcing, exploration, and asking the right questions. The LLM does all the grunt work — the summarizing, cross-referencing, filing, and bookkeeping that makes a knowledge base actually useful over time. In practice, I have the LLM agent open on one side and Obsidian open on the other. The LLM makes edits based on our conversation, and I browse the results in real time — following links, checking the graph view, reading the updated pages. Obsidian is the IDE; the LLM is the programmer; the wiki is the codebase.

This can apply to a lot of different contexts. A few examples:

- **Personal**: tracking your own goals, health, psychology, self-improvement — filing journal entries, articles, podcast notes, and building up a structured picture of yourself over time.
- **Research**: going deep on a topic over weeks or months — reading papers, articles, reports, and incrementally building a comprehensive wiki with an evolving thesis.
- **Reading a book**: filing each chapter as you go, building out pages for characters, themes, plot threads, and how they connect. By the end you have a rich companion wiki. Think of fan wikis like [Tolkien Gateway](https://tolkiengateway.net/wiki/Main_Page) — thousands of interlinked pages covering characters, places, events, languages, built by a community of volunteers over years. You could build something like that personally as you read, with the LLM doing all the cross-referencing and maintenance.
- **Business/team**: an internal wiki maintained by LLMs, fed by Slack threads, meeting transcripts, project documents, customer calls. Possibly with humans in the loop reviewing updates. The wiki stays current because the LLM does the maintenance that no one on the team wants to do.
- **Competitive analysis, due diligence, trip planning, course notes, hobby deep-dives** — anything where you're accumulating knowledge over time and want it organized rather than scattered.

## Architecture

There are three layers:

**Raw sources** — your curated collection of source documents. Articles, papers, images, data files. These are immutable — the LLM reads from them but never modifies them. This is your source of truth.

**The wiki** — a directory of LLM-generated markdown files. Summaries, entity pages, concept pages, comparisons, an overview, a synthesis. The LLM owns this layer entirely. It creates pages, updates them when new sources arrive, maintains cross-references, and keeps everything consistent. You read it; the LLM writes it.

**The schema** — a document (e.g. CLAUDE.md for Claude Code or AGENTS.md for Codex) that tells the LLM how the wiki is structured, what the conventions are, and what workflows to follow when ingesting sources, answering questions, or maintaining the wiki. This is the key configuration file — it's what makes the LLM a disciplined wiki maintainer rather than a generic chatbot. You and the LLM co-evolve this over time as you figure out what works for your domain.

## Operations

**Ingest.** You drop a new source into the raw collection and tell the LLM to process it. An example flow: the LLM reads the source, discusses key takeaways with you, writes a summary page in the wiki, updates the index, updates relevant entity and concept pages across the wiki, and appends an entry to the log. A single source might touch 10-15 wiki pages. Personally I prefer to ingest sources one at a time and stay involved — I read the summaries, check the updates, and guide the LLM on what to emphasize. But you could also batch-ingest many sources at once with less supervision. It's up to you to develop the workflow that fits your style and document it in the schema for future sessions.

**Query.** You ask questions against the wiki. The LLM searches for relevant pages, reads them, and synthesizes an answer with citations. Answers can take different forms depending on the question — a markdown page, a comparison table, a slide deck (Marp), a chart (matplotlib), a canvas. The important insight: **good answers can be filed back into the wiki as new pages.** A comparison you asked for, an analysis, a connection you discovered — these are valuable and shouldn't disappear into chat history. This way your explorations compound in the knowledge base just like ingested sources do.

**Lint.** Periodically, ask the LLM to health-check the wiki. Look for: contradictions between pages, stale claims that newer sources have superseded, orphan pages with no inbound links, important concepts mentioned but lacking their own page, missing cross-references, data gaps that could be filled with a web search. The LLM is good at suggesting new questions to investigate and new sources to look for. This keeps the wiki healthy as it grows.

## Indexing and logging

Two special files help the LLM (and you) navigate the wiki as it grows. They serve different purposes:

**index.md** is content-oriented. It's a catalog of everything in the wiki — each page listed with a link, a one-line summary, and optionally metadata like date or source count. Organized by category (entities, concepts, sources, etc.). The LLM updates it on every ingest. When answering a query, the LLM reads the index first to find relevant pages, then drills into them. This works surprisingly well at moderate scale (~100 sources, ~hundreds of pages) and avoids the need for embedding-based RAG infrastructure.

**log.md** is chronological. It's an append-only record of what happened and when — ingests, queries, lint passes. A useful tip: if each entry starts with a consistent prefix (e.g. `## [2026-04-02] ingest | Article Title`), the log becomes parseable with simple unix tools — `grep "^## \[" log.md | tail -5` gives you the last 5 entries. The log gives you a timeline of the wiki's evolution and helps the LLM understand what's been done recently.

## Optional: CLI tools

At some point you may want to build small tools that help the LLM operate on the wiki more efficiently. A search engine over the wiki pages is the most obvious one — at small scale the index file is enough, but as the wiki grows you want proper search. [qmd](https://github.com/tobi/qmd) is a good option: it's a local search engine for markdown files with hybrid BM25/vector search and LLM re-ranking, all on-device. It has both a CLI (so the LLM can shell out to it) and an MCP server (so the LLM can use it as a native tool). You could also build something simpler yourself — the LLM can help you vibe-code a naive search script as the need arises.

## Tips and tricks

- **Obsidian Web Clipper** is a browser extension that converts web articles to markdown. Very useful for quickly getting sources into your raw collection.
- **Download images locally.** In Obsidian Settings → Files and links, set "Attachment folder path" to a fixed directory (e.g. `raw/assets/`). Then in Settings → Hotkeys, search for "Download" to find "Download attachments for current file" and bind it to a hotkey (e.g. Ctrl+Shift+D). After clipping an article, hit the hotkey and all images get downloaded to local disk. This is optional but useful — it lets the LLM view and reference images directly instead of relying on URLs that may break. Note that LLMs can't natively read markdown with inline images in one pass — the workaround is to have the LLM read the text first, then view some or all of the referenced images separately to gain additional context. It's a bit clunky but works well enough.
- **Obsidian's graph view** is the best way to see the shape of your wiki — what's connected to what, which pages are hubs, which are orphans.
- **Marp** is a markdown-based slide deck format. Obsidian has a plugin for it. Useful for generating presentations directly from wiki content.
- **Dataview** is an Obsidian plugin that runs queries over page frontmatter. If your LLM adds YAML frontmatter to wiki pages (tags, dates, source counts), Dataview can generate dynamic tables and lists.
- The wiki is just a git repo of markdown files. You get version history, branching, and collaboration for free.

## Why this works

The tedious part of maintaining a knowledge base is not the reading or the thinking — it's the bookkeeping. Updating cross-references, keeping summaries current, noting when new data contradicts old claims, maintaining consistency across dozens of pages. Humans abandon wikis because the maintenance burden grows faster than the value. LLMs don't get bored, don't forget to update a cross-reference, and can touch 15 files in one pass. The wiki stays maintained because the cost of maintenance is near zero.

The human's job is to curate sources, direct the analysis, ask good questions, and think about what it all means. The LLM's job is everything else.

The idea is related in spirit to Vannevar Bush's Memex (1945) — a personal, curated knowledge store with associative trails between documents. Bush's vision was closer to this than to what the web became: private, actively curated, with the connections between documents as valuable as the documents themselves. The part he couldn't solve was who does the maintenance. The LLM handles that.


## Note

This document is intentionally abstract. It describes the idea, not a specific implementation. The exact directory structure, the schema conventions, the page formats, the tooling — all of that will depend on your domain, your preferences, and your LLM of choice. Everything mentioned above is optional and modular — pick what's useful, ignore what isn't. For example: your sources might be text-only, so you don't need image handling at all. Your wiki might be small enough that the index file is all you need, no search engine required. You might not care about slide decks and just want markdown pages. You might want a completely different set of output formats. The right way to use this is to share it with your LLM agent and work together to instantiate a version that fits your needs. The document's only job is to communicate the pattern. Your LLM can figure out the rest.


# LLM Wiki v2

A pattern for building personal knowledge bases using LLMs. Extended with lessons from building [agentmemory](https://github.com/rohitg00/agentmemory), a persistent memory engine for AI coding agents.

This builds on [Andrej Karpathy's original LLM Wiki idea file](https://gist.github.com/karpathy/442a6bf555914893e9891c11519de94f). Everything in the original still applies. This document adds what we learned running the pattern in production: what breaks at scale, what's missing, and what separates a wiki that stays useful from one that rots.

## What the original gets right

The core insight is correct: **stop re-deriving, start compiling.** RAG retrieves and forgets. A wiki accumulates and compounds. The three-layer architecture (raw sources, wiki, schema) works. The operations (ingest, query, lint) cover the basics. If you haven't read the original, start there.

What follows is what we found after building and running this pattern across thousands of sessions.

## The missing layer: memory lifecycle

The original treats all wiki content as equally valid forever. In practice, knowledge has a lifecycle. A bug you discovered last week matters more than one from six months ago. A pattern you've seen twelve times is more reliable than one you've seen once. A claim from a newer source should weaken an older one automatically.

**Confidence scoring.** Every fact in the wiki should carry a confidence score: how many sources support it, how recently it was confirmed, whether anything contradicts it. When the LLM writes "Project X uses Redis for caching," that claim should know it came from two sources, was last confirmed three weeks ago, and sits at confidence 0.85. Confidence decays with time and strengthens with reinforcement. This turns the wiki from a flat collection of equally-weighted claims into a living model where the LLM can say "I'm fairly sure about X but less sure about Y."

**Supersession.** When new information contradicts or updates an existing claim, the old claim shouldn't just sit there with a note. The new one should explicitly supersede it. Linked, timestamped, old version preserved but marked stale. Version control for knowledge, not just for files.

**Forgetting.** Not everything should live forever. A wiki that never forgets becomes noisy. Implement a retention curve: facts that were important once but haven't been accessed or reinforced in months should gradually fade. Not deleted, but deprioritized. The LLM equivalent of moving something to a bottom drawer. Ebbinghaus's forgetting curve works well here: retention decays exponentially with time, but each reinforcement (access, confirmation from a new source) resets the curve. Architecture decisions decay slowly. Transient bugs decay fast.

**Consolidation tiers.** Raw observations aren't the same as established facts. Build a pipeline:
- **Working memory**: recent observations, not yet processed
- **Episodic memory**: session summaries, compressed from raw observations
- **Semantic memory**: cross-session facts, consolidated from episodes
- **Procedural memory**: workflows and patterns, extracted from repeated semantics

Each tier is more compressed, more confident, and longer-lived than the one below it. The LLM promotes information up the tiers as evidence accumulates. This is how you go from "I saw this once" to "this is how things work."

## Beyond flat pages: the knowledge graph

The original wiki is pages with wikilinks. That works, but you're leaving structure on the table. What you actually want is a typed knowledge graph layered on top of the pages.

**Entity extraction.** When the LLM ingests a source, it shouldn't just write prose. It should extract structured entities. People, projects, libraries, concepts, files, decisions. Each entity gets a type, attributes, and relationships to other entities. "React" is a library. "Auth migration" is a project. "Sarah" is a person who owns the auth migration and has opinions about React.

**Typed relationships.** Not all connections are equal. "uses," "depends on," "contradicts," "caused," "fixed," "supersedes" carry different semantic weight. A link that says "A relates to B" is less useful than "A caused B, confirmed by 3 sources, confidence 0.9."

**Graph traversal for queries.** When someone asks "what's the impact of upgrading Redis?", the LLM shouldn't just keyword-search. It should start at the Redis node, walk outward through "depends on" and "uses" edges, and find everything downstream. This catches connections that keyword search misses.

The graph doesn't replace the wiki pages. It augments them. Pages are for reading. The graph is for navigation and discovery.

## Search that actually scales

The original relies on `index.md`, a single file cataloging every page. This works up to maybe 100-200 pages. Beyond that, the index itself becomes too long for the LLM to read in one pass, and you need real search.

**Hybrid search.** The best approach combines three streams:
- **BM25** (keyword matching with stemming and synonym expansion)
- **Vector search** (semantic similarity via embeddings)
- **Graph traversal** (entity-aware relationship walking)

Fuse the results with reciprocal rank fusion. Each stream catches things the others miss. BM25 finds exact terms. Vectors find semantic similarity. The graph finds structural connections. Together they beat any single approach.

Keep `index.md` as a human-readable catalog, but don't rely on it as the LLM's primary search mechanism past ~100 pages.

## Automation: from manual to event-driven

The biggest practical gap in the original is that everything is manual. You drop a source and tell the LLM to process it. You remember to run lint periodically. You decide when to file an answer back.

In practice, you want hooks. Events that fire automatically:

- **On new source**: auto-ingest, extract entities, update graph, update index
- **On session start**: load relevant context from the wiki based on recent activity
- **On session end**: compress the session into observations, file insights
- **On query**: check if the answer is worth filing back (quality score > threshold)
- **On memory write**: check for contradictions with existing knowledge, trigger supersession
- **On schedule**: periodic lint, consolidation, retention decay

The human should still be in the loop for curation and direction. But the bookkeeping, the part that makes people abandon wikis, should be fully automated.

## Quality and self-correction

Not all LLM-generated content is good. Without quality controls, the wiki accumulates noise.

**Score everything.** Every piece of content the LLM writes should get a quality score. Is it well-structured? Does it cite sources? Is it consistent with the rest of the wiki? You can have the LLM self-evaluate, or use a second pass with a different prompt. Content below a threshold gets flagged for review or rewritten.

**Self-healing.** The lint operation from the original should be more than a suggestion. It should automatically fix what it can. Orphan pages get linked or flagged. Stale claims get marked. Broken cross-references get repaired. The wiki should tend toward health on its own, not only when you remember to ask.

**Contradiction resolution.** The original mentions flagging contradictions. That's step one. Step two is resolving them. The LLM should propose which claim is more likely correct based on source recency, source authority, and the number of supporting observations. The human can override, but the default behavior should usually be right.

## Multi-agent and collaboration

The original is single-user, single-agent. Many real use cases involve multiple agents or multiple people contributing to the same knowledge base.

**Mesh sync.** If multiple agents are working in parallel (different coding sessions, different research threads), their observations need to merge into a shared wiki. Last-write-wins works for most cases. For conflicts, timestamp-based resolution with manual override.

**Shared vs. private.** Some knowledge is personal (my preferences, my workflow). Some is shared (project architecture, team decisions). The wiki needs scoping. Private observations that roll up into shared knowledge when promoted.

**Work coordination.** When multiple agents work on the same knowledge base, they need lightweight coordination. Who's working on what. What's blocked. What's done. Not a full task management system, just enough to prevent duplicate work and track progress.

## Privacy and governance

The original doesn't mention this, but it matters. Sources often contain sensitive information: API keys, credentials, private conversations, PII.

**Filter on ingest.** Before anything hits the wiki, strip sensitive data. API keys, tokens, passwords, anything marked private. This should be automatic, not something you remember to do.

**Audit trail.** Every operation on the wiki (ingest, edit, delete, query) should be logged with a timestamp, what changed, and why. This is your accountability layer. When something looks wrong in the wiki, the audit trail tells you how it got there.

**Bulk operations with governance.** As the wiki grows, you'll want to bulk-delete stale content, export subsets, or merge duplicate entities. These operations should be audited and reversible.

## Crystallization: compounding from exploration

The original mentions that "good answers can be filed back into the wiki as new pages." This can be taken further.

**Crystallization** is the process of taking a completed chain of work (a research thread, a debugging session, an analysis) and automatically distilling it into a structured digest. What was the question? What did we find? What files/entities were involved? What lessons emerged? This digest becomes a first-class wiki page, and the lessons get extracted as standalone facts that strengthen the knowledge base.

Your explorations are a source, just like an article or a paper. The wiki should treat them that way. Ingest the results, update the graph, strengthen or challenge existing claims.

## Output formats beyond markdown

The original mentions Marp for slide decks and matplotlib for charts. The wiki's output shouldn't be limited to markdown pages. Depending on the query, the right output might be:

- A comparison table
- A timeline visualization
- A dependency graph
- A slide deck for presenting findings
- A structured data export (JSON, CSV) for further analysis
- A brief for someone else on your team

The wiki is the knowledge store. The output format depends on the audience and the question.

## The schema is the real product

The original implies this but it's worth being direct: **the schema document (CLAUDE.md, AGENTS.md) is the most important file in the system.** It's what turns a generic LLM into a disciplined knowledge worker. It encodes:

- What types of entities and relationships exist in your domain
- How to ingest different kinds of sources
- When to create a new page vs. update an existing one
- What quality standards to apply
- How to handle contradictions
- What the consolidation schedule looks like
- What's private vs. shared

You and the LLM co-evolve this document over time. The first version will be rough. After a few dozen sources and a few lint passes, you'll have a schema that reflects how your domain actually works. That schema is transferable. Share it with someone else working on a similar domain and they get a running start.

## Implementation spectrum

All of this is modular. You don't need everything on day one.

**Minimal viable wiki**: raw sources + wiki pages + index.md + a schema that describes ingest/query/lint workflows. This is roughly what the original describes. It works. Start here.

**Add lifecycle**: confidence scoring, supersession, basic retention decay. This prevents the wiki from becoming a junk drawer.

**Add structure**: entity extraction, typed relationships, knowledge graph. This makes queries better and surfaces connections you'd miss with flat pages.

**Add automation**: hooks for auto-ingest, auto-lint, context injection. This is where the maintenance burden drops to near zero.

**Add scale**: hybrid search, consolidation tiers, quality scoring. This is what you need when the wiki grows past a few hundred pages.

**Add collaboration**: mesh sync, shared/private scoping, work coordination. This is for teams or multi-agent setups.

Pick your entry point based on your needs. The pattern works at every level.

## Why this matters

Karpathy's original insight stands: the bottleneck is bookkeeping, and LLMs eliminate that bottleneck. What we've added is the machinery that keeps the wiki healthy as it scales. Lifecycle management so knowledge doesn't rot. Structure so connections aren't lost. Automation so humans stay focused on thinking rather than filing. Quality controls so the wiki earns trust over time.

The Memex is finally buildable. Not because we have better documents or better search, but because we have librarians that actually do the work.

---

*This document extends [Andrej Karpathy's LLM Wiki](https://gist.github.com/karpathy/442a6bf555914893e9891c11519de94f) with patterns proven in [agentmemory](https://github.com/rohitg00/agentmemory), a persistent memory engine for AI agents built on [iii-engine](https://github.com/iii-hq/iii). The original idea file is the foundation; this adds what we learned building the engine.*

