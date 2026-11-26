/** @type {import('vite').UserConfig} */

export default {
    build: {
        lib: {
            entry: {
                'graph': 'src/wcs/graph.ts',
                'staticgraph': 'src/wcs/staticwrapper.ts',
                'dynamicgraph': 'src/wcs/dynamicwrapper.ts'
            },
            fileName: (format, entryName) => `intdot-${entryName}.${format}.js`,
            cssFileName: 'intdot-style',
            formats: ['es']
        },
        rollupOptions: {
            external: [],
            output: {
                // Modules imported by several entries go into shared chunks.
                // Name them like the entries, so that they are copied to
                // data/js and ignored by git along with them (see Makefile).
                chunkFileNames: 'intdot-[name].es.js'
            }
        }
    }
}