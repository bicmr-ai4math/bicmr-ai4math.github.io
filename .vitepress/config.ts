import { defineConfig } from "vitepress";

import markdownItKatex from "./plugin/markdown-it-katex";

// https://vitepress.dev/reference/site-config
export default defineConfig({
  markdown: {
    config: (md) => {
      md.use(markdownItKatex);
    },
  },
  vue: {
    template: {
      compilerOptions: {
        isCustomElement: (tag) => katexCustomElements.includes(tag),
      },
    },
  },

  title: "PKU BiCMR AI for Math",
  description:
    'BiCMR "AI for Mathematics: Formalization and Theorem Proving" Seminar Homepage',
  themeConfig: {
    // https://vitepress.dev/reference/default-theme-config
    nav: [
      { text: "Home", link: "/" },

      { text: "Lean4 Q&A", link: "/lean4-qa" },
      {
        text: "Team Exercises",
        link: "/team-exercises",
      },
      { text: "Research Projects", link: "/research-projects" },

      { text: "About", link: "/about" },
    ],

    sidebar: [
      { text: "About", link: "/about" },

      { text: "Lean4 Q&A", link: "/lean4-qa" },
      {
        text: "Team Exercises",
        link: "/team-exercises",
      },
      { text: "Research Projects", link: "/research-projects" },
    ],

    socialLinks: [
      { icon: "github", link: "https://github.com/bicmr-ai4math" },
    ],
  },

  head: [
    [
      "link",
      {
        rel: "stylesheet",
        href: "https://cdn.jsdelivr.net/npm/katex@0.16.8/dist/katex.min.css",
        crossorigin: "",
      },
    ],
  ],
});

// hack. See https://github.com/vuejs/vitepress/issues/529#issuecomment-1151186631
const katexCustomElements = [
  "math",
  "maction",
  "maligngroup",
  "malignmark",
  "menclose",
  "merror",
  "mfenced",
  "mfrac",
  "mi",
  "mlongdiv",
  "mmultiscripts",
  "mn",
  "mo",
  "mover",
  "mpadded",
  "mphantom",
  "mroot",
  "mrow",
  "ms",
  "mscarries",
  "mscarry",
  "mscarries",
  "msgroup",
  "mstack",
  "mlongdiv",
  "msline",
  "mstack",
  "mspace",
  "msqrt",
  "msrow",
  "mstack",
  "mstack",
  "mstyle",
  "msub",
  "msup",
  "msubsup",
  "mtable",
  "mtd",
  "mtext",
  "mtr",
  "munder",
  "munderover",
  "semantics",
  "math",
  "mi",
  "mn",
  "mo",
  "ms",
  "mspace",
  "mtext",
  "menclose",
  "merror",
  "mfenced",
  "mfrac",
  "mpadded",
  "mphantom",
  "mroot",
  "mrow",
  "msqrt",
  "mstyle",
  "mmultiscripts",
  "mover",
  "mprescripts",
  "msub",
  "msubsup",
  "msup",
  "munder",
  "munderover",
  "none",
  "maligngroup",
  "malignmark",
  "mtable",
  "mtd",
  "mtr",
  "mlongdiv",
  "mscarries",
  "mscarry",
  "msgroup",
  "msline",
  "msrow",
  "mstack",
  "maction",
  "semantics",
  "annotation",
  "annotation-xml",
];
