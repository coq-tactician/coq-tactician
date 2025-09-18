from setuptools import setup, Extension
import subprocess
import os
from shutil import copyfile
import capnp

from Cython.Build import cythonize

def capnp2cython():

    api_file = "pytact/graph_api.capnp"
    cython_file_pyx = api_file.replace('.', '_')+'_cython.pyx'
    cython_file_pxd = api_file.replace('.', '_')+'_cython.pxd'
    template_files = ["pytact/templates/capnp_cython.pyx", "pytact/templates/capnp_cython.pxd"]

    # Poor man's make
    target_time = min([(os.path.getmtime(f) if os.path.exists(f) else 0) for f in
                        [api_file+'.c++', api_file+'.cpp', api_file+'.h', cython_file_pyx, cython_file_pxd]])
    source_time = max([os.path.getmtime(f) for f in [api_file] + template_files])
    if target_time < source_time:
        print(subprocess.check_output(["capnpc", "-oc++", api_file]))
        subprocess.check_output(["capnpc", "-o./pytact/generate_api.py", api_file])

        copyfile(api_file + '.c++', api_file + '.cpp')

    capnp_loc = os.path.abspath(os.path.join(list(capnp.__path__)[0], '../'))
    return cythonize([
        Extension(
            name = "pytact.graph_api_capnp_cython",
            sources = [cython_file_pyx],
            extra_compile_args=["-O3", "-std=c++14"],
            include_dirs=[capnp_loc]
        ),
        Extension(
            name = "pytact.data_reader",
            sources = ['pytact/data_reader.pyx'],
            extra_compile_args=["-O3", "-std=c++14"],
            include_dirs=[capnp_loc]
        )])

setup(
    ext_modules = capnp2cython()
)
