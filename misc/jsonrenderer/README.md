Having your own Tamarin graph output
====================================

The option '--with-json=<your-JSON-renderer>' in interactive mode causes Tamarin 
to export constraint systems into individual files in JSON format into the 
temporary directory (/tmp/tamarin-prover-cache/img). Tamarin then uses <your-JSON-renderer> 
to convert a JSON file to a PNG file which is displayed in the GUI.

The two programs

`json_renderer.py` and
`json_renderer_compact.py`

are proof-of-concept examples of renderers using the dot command of Graphviz.

Note that the option '--with-json' currently works neither with the option '--diff' 
nor in non-interactive mode.

Usage
-----

The JSON renderer must take the name of the output PNG file as its first parameter and
the input JSON file as its second parameter, e.g.

    json_renderer.py test1.png test1.json

Example for the use of the '--with-json' option:

    tamarin-prover interactive \
    --with-json=/home/cas/src/tamarin-prover/misc/jsonrenderer/json_renderer.py .


