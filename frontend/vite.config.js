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
            external: []
        }
    }
}