import path from 'path';
import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';

export default defineConfig({
    plugins: [
        {
            // Plugin code is from https://github.com/chaosprint/vite-plugin-cross-origin-isolation
            name: 'configure-response-headers',
            configureServer: (server) => {
                server.middlewares.use((_req, res, next) => {
                    res.setHeader('Cross-Origin-Embedder-Policy', 'require-corp');
                    res.setHeader('Cross-Origin-Opener-Policy', 'same-origin');
                    next();
                });
            },
        },
        react(),
    ],
    resolve: {
        alias: {
            '@': path.resolve(__dirname, './src'),
        },
    },
    build: {
        chunkSizeWarningLimit: 1000,
        rollupOptions: {
            onwarn(warning, warn) {
                if (warning.code === 'MODULE_LEVEL_DIRECTIVE') {
                    return;
                }
                warn(warning);
            },
        },
    },
    preview: {
        port: 5173,
        strictPort: true,
        host: '0.0.0.0',
        allowedHosts: true,
        proxy: {
            '/diff-limboole': {
                target: 'http://fmp-limboole-diff-api:8080',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/diff-limboole/, ''),
            },
            '/nuxmv': {
                target: 'http://fmp-nuxmv-api:8080',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/nuxmv/, ''),
            },
            '/smt': {
                target: 'http://fmp-z3-api:8080',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/smt/, ''),
            },
            '/diff-smt': {
                target: 'http://fmp-diff-smt-api:8080',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/diff-smt/, ''),
            },
            '/alloy': {
                target: 'http://fmp-alloy-api:8080',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/alloy/, ''),
            },
            '/spectra': {
                target: 'http://fmp-spectra-api:8080',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/spectra/, ''),
            },
            '/dafny': {
                target: 'http://fmp-dafny-api:8080',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/dafny/, ''),
            },
            '/lsp-dafny': {
                target: 'ws://fmp-dafny-lsp:8080',
                changeOrigin: true,
                secure: false,
                ws: true,
                rewrite: (path) => path.replace(/^\/lsp-dafny/, ''),
            },
        },
    },
    server: {
        watch: {
            usePolling: true,
        },
        port: 5173,
        strictPort: true,
        host: '0.0.0.0',
        allowedHosts: true,
        proxy: {
            '/diff-limboole': {
                target: 'http://localhost:8051',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/diff-limboole/, ''),
            },
            '/nuxmv': {
                target: 'http://localhost:8081',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/nuxmv/, ''),
            },
            '/smt': {
                target: 'http://localhost:8082',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/smt/, ''),
            },
            '/diff-smt': {
                target: 'http://localhost:8052',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/diff-smt/, ''),
            },
            '/alloy': {
                target: 'http://localhost:8080',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/alloy/, ''),
            },
            '/spectra': {
                target: 'http://localhost:8083',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/spectra/, ''),
            },
            '/dafny': {
                target: 'http://localhost:8085',
                changeOrigin: true,
                secure: false,
                rewrite: (path) => path.replace(/^\/dafny/, ''),
            },
            '/lsp-dafny': {
                target: 'ws://localhost:8091',
                changeOrigin: true,
                secure: false,
                ws: true,
                rewrite: (path) => path.replace(/^\/lsp-dafny/, ''),
            },
        },
    },
});
