import { defineConfig } from "vitepress";

// https://vitepress.dev/reference/site-config
export default defineConfig({
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
    ["link", {
      rel: "stylesheet",
      href: "https://cdn.jsdelivr.net/npm/katex@0.16.8/dist/katex.min.css",
      crossorigin: "",
    }],
    [
      "script",
      { type: "module", id: "katex-render" },
      `
      import renderMathInElement from "https://cdn.jsdelivr.net/npm/katex@0.16.8/dist/contrib/auto-render.mjs";
      renderMathInElement(document.body, {
        delimiters: [
          { left: "$$", right: "$$", display: true },
          { left: "$", right: "$", display: false },
        ],
        throwOnError: false,
      });
    `,
    ],
  ],
});
