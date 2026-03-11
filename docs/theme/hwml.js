// HWML syntax highlighting
// Since this loads after book.js has already called highlightAll(),
// we need to register languages and re-highlight

(function () {
  if (typeof hljs === 'undefined') return;

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

  // Re-highlight code blocks that use our custom languages
  document.querySelectorAll('code.language-hwml, code.language-hwmlc').forEach(function (block) {
    hljs.highlightElement(block);
  });
})();

