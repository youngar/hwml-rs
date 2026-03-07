// Highlight.js syntax definition for HWML languages
// This file defines syntax highlighting for both hwml (surface) and hwmlc (core)

(function(hljs) {
  // Core language (hwmlc) definition
  hljs.registerLanguage('hwmlc', function(hljs) {
    return {
      name: 'HWML Core',
      keywords: {
        keyword: 'prim const tcon dcon where',
        built_in: 'U0 U1 U2 Bit',
        literal: '0 1'
      },
      contains: [
        // Line comments
        hljs.COMMENT('//', '$'),
        // Block comments
        hljs.COMMENT('/\\*', '\\*/'),
        // Primitives ($Name)
        {
          className: 'type',
          begin: '\\$[A-Z][a-zA-Z0-9_]*'
        },
        // Constants (@Name)
        {
          className: 'title',
          begin: '@[A-Z][a-zA-Z0-9_]*'
        },
        // Variables (%name)
        {
          className: 'variable',
          begin: '%[a-z][a-zA-Z0-9_]*'
        },
        // Metavariables (?name)
        {
          className: 'meta',
          begin: '\\?[a-z][a-zA-Z0-9_]*'
        },
        // Hardware lift operator (^)
        {
          className: 'operator',
          begin: '\\^'
        },
        // Signal type (^s)
        {
          className: 'built_in',
          begin: '\\^s'
        },
        // Arrows
        {
          className: 'operator',
          begin: '->'
        },
        // Strings
        hljs.QUOTE_STRING_MODE
      ]
    };
  });

  // Surface language (hwml) definition - placeholder for now
  hljs.registerLanguage('hwml', function(hljs) {
    return {
      name: 'HWML Surface',
      keywords: {
        keyword: 'let in if then else match with type data where',
        built_in: 'Bit Nat Bool',
        literal: 'true false 0 1'
      },
      contains: [
        hljs.COMMENT('//', '$'),
        hljs.COMMENT('/\\*', '\\*/'),
        hljs.QUOTE_STRING_MODE,
        hljs.C_NUMBER_MODE
      ]
    };
  });
})(window.hljs);

