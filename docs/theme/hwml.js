// HWML syntax highlighting for mdBook
// Uses the "second pass" pattern: register languages, then highlight blocks that book.js missed

window.addEventListener('load', function () {
  if (typeof hljs === 'undefined') return;

  // Register HWML Core language
  hljs.registerLanguage('hwmlc', function (hljs) {
    return {
      name: 'HWML Core',
      keywords: {
        keyword: 'prim const tcon dcon where',
        built_in: 'U0 U1 U2 Bit',
        literal: '0 1'
      },
      contains: [
        hljs.COMMENT('//', '$'),
        hljs.COMMENT('/\\*', '\\*/'),
        { className: 'type', begin: '\\$[A-Z][a-zA-Z0-9_]*' },
        { className: 'title', begin: '@[A-Z][a-zA-Z0-9_]*' },
        { className: 'variable', begin: '%[a-z][a-zA-Z0-9_]*' },
        { className: 'meta', begin: '\\?[a-z][a-zA-Z0-9_]*' },
        { className: 'operator', begin: '\\^' },
        { className: 'built_in', begin: '\\^s' },
        { className: 'operator', begin: '->' },
        hljs.QUOTE_STRING_MODE
      ]
    };
  });

  // Register HWML Surface language
  hljs.registerLanguage('hwml', function (hljs) {
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

  // Second pass: highlight blocks that book.js missed
  // (mdBook uses hljs v10.x, so we use highlightBlock)
  document.querySelectorAll('code.language-hwml, code.language-hwmlc').forEach(function (block) {
    hljs.highlightBlock(block);
  });
});

