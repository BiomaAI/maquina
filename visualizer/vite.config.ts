import { defineConfig, loadEnv } from "vite";

export default defineConfig(({ mode }) => {
  const environment = loadEnv(mode, ".", "");
  return {
    base: environment.VITE_MAQUINA_BASE ?? "/",
    build: {
      target: "es2022",
      sourcemap: false,
      chunkSizeWarningLimit: 600,
    },
    test: {
      environment: "node",
      include: ["src/**/*.test.ts"],
    },
  };
});
