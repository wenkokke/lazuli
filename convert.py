from functools import reduce
from getopt import getopt, GetoptError
from pathlib import Path
from sys import argv, exit
from tensorflow.keras.models import load_model

def convert_real(x):
    """Pretty-print a float as an Liquid Haskell real."""
    if x >= 0.0:
        return '{0:.8f}'.format(x)
    else:
        return '-{0:.8f}'.format(abs(x))

def convert_matrix_row(row):
    """Pretty-print a row of floats as an Liquid Haskell list."""
    size = len(row)
    return '{size} |> [{vals}]'.format(
        size=size,
        vals=', '.join(map(convert_real, row)))

def convert_matrix(matrix):
    """Pretty-print a Keras matrix as a Lazuli matrix."""
    rows = matrix.shape[0]
    cols = matrix.shape[1]
    return '({rows} >< {cols})\n[ {vals}\n]'.format(
        rows=rows,
        cols=cols,
        vals='\n, '.join(map(convert_matrix_row, matrix.tolist())))

def convert_vector(vector):
    """Pretty-print a Keras vector as a Lazuli vector."""
    row = vector.tolist()[0]
    size = len(row)
    return '{size} :> [{vals}]'.format(
        size=size,
        vals=', '.join(map(convert_real, row)))

def convert_activation(activation):
    """Pretty-print a Keras activation function as a Lazuli constructor."""
    return {
        'linear': 'Linear',
        'relu': 'ReLU',
        'sigmoid': 'Sigmoid',
        'softmax': 'Softmax'}[activation]

def convert_layer(index, layer):
    """Pretty-print a Keras layer as a Lazuli definition."""
    params = layer.get_weights()
    weights = params[0]
    rows = weights.shape[0]
    cols = weights.shape[1]
    biases = params[1].reshape((1, -1))
    activation = layer.get_config()['activation']
    return ('{{-@ reflect layer{index} @-}}\n'
            '{{-@ layer{index} :: LayerN {rows} {cols} @-}}\n'
            'layer{index} :: Layer\n'
            'layer{index} = Layer\n'
            '  {{ weights    = {weights}\n'
            '  , biases     = {biases}\n'
            '  , activation = {activation}\n'
            '  }}').format(
                index=index,
                rows=rows,
                cols=cols,
                weights=convert_matrix(weights).replace('\n','\n'+17*' '),
                biases=convert_vector(biases),
                activation=convert_activation(activation))

def convert_layer_list(layers, n_in, n_out):
    layers[-1] = 'NLast {}'.format(layers[-1])
    layer_list = reduce(lambda x, y: 'NStep {} ({})'.format(y, x),reversed(layers))
    return ('{{-@ reflect model @-}}\n'
            '{{-@ model :: NetworkN {n_in} {n_out} @-}}\n'
            'model :: Network\n'
            'model = {layer_list}').format(
                n_in=n_in, n_out=n_out, layer_list=layer_list, n_layers=len(layers))

def convert_model(ifile, ofile):
    """Pretty-print a Keras models from a H5 file."""

    # Open output file
    with open(ofile, 'w') as os:

        # Print file preamble
        module_name = Path(ofile).resolve().stem
        os.write(('{{-@ LIQUID "--reflection" @-}}\n'
                  '{{-@ LIQUID "--ple"        @-}}\n'
                  '\n'
                  'module {} where\n'
                  '\n'
                  'import           Lazuli.LinearAlgebra\n'
                  'import qualified Lazuli.LinearAlgebra.Internal\n'
                  'import           Lazuli.Network\n'
                  'import qualified Lazuli.Prelude\n'
                  '\n').format(module_name))

        # Load model
        model = load_model(ifile)

        # Print layer definitions
        layers = []
        n_in = None
        n_out = None
        for index, layer in enumerate(model.layers):
            params = layer.get_weights()
            if len(params) > 0:
                weights = params[0]
                rows = weights.shape[0]
                cols = weights.shape[1]
                layers.append('layer{}'.format(index))
                if n_in is None: n_in = rows
                n_out = cols
                os.write(convert_layer(index, layer))
                os.write('\n\n')

        # Print model definition
        os.write(convert_layer_list(layers, n_in, n_out))

def help():
    print('Usage: python convert.py -i [input_file] -o [output_file]')
    exit(2)

if __name__ == "__main__":
    ifile = None
    ofile = None
    try:
        opts, args = getopt(argv[1:], "hi:o:", [])
    except GetoptError:
        help()
    for opt, arg in opts:
        if opt == '-h': help()
        if opt == '-i': ifile = arg
        if opt == '-o': ofile = arg
    if Path(ifile).is_file():
        convert_model(ifile, ofile)
    elif ifile is None:
        help()
    else:
        print("Error: file '" + path + "' not found.")
        exit(3)
