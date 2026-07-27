import { defineConfig } from "vite";

export default defineConfig({
  build: {
    emptyOutDir: false,
    lib: {
      entry: "bench/json-to-dot.ts",
      formats: ["es"],
      fileName: () => "json-to-dot",
    },
    outDir: "bench/dist",
    rollupOptions: {
      external: ["node:fs/promises", "node:path", "node:perf_hooks"],
    },
    ssr: true,
    target: "node20",
  },
});