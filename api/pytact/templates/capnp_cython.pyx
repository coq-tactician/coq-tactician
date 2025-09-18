# distutils: language = c++
# distutils: libraries = capnpc capnp capnp-rpc
# distutils: sources = pytact/graph_api.capnp.cpp
# cython: c_string_type = str
# cython: c_string_encoding = default
# cython: embedsignature = True
# cython: language_level = 3

import os
import capnp
import pytact.graph_api_capnp
from capnp.lib.capnp cimport SchemaParser

def loadCompiledTypes(SchemaParser schema_parser):
    cdef C_SchemaParser* c_schema_parser = <C_SchemaParser*>schema_parser.thisptr
    {%- for c in classes %}
    c_schema_parser.loadCompiledTypeAndDependencies{{ c.cython_name }}()
    {%- endfor %}

loadCompiledTypes(capnp.lib.capnp._global_schema_parser)

{%- for c in classes %}

cdef class {{ c.cython_name }}_Reader:
    {%- if c.doc != "" %}
    """
    {{ c.doc | indent(4) }}
    """
    {%- endif %}

    def __init__(self, _DynamicStructReader dyn):
        self.source = (<C_DynamicStruct_Reader>dyn.thisptr).as{{ c.cython_name }}()
        self.root = dyn # We keep a referene to the root in order to prevent it from being garbage collected

    @staticmethod
    cdef init(C_{{ c.cython_name }}_Reader source, object root):
        cdef {{ c.cython_name }}_Reader wrapper = {{ c.cython_name }}_Reader.__new__({{ c.cython_name }}_Reader)
        wrapper.source = source
        wrapper.root = root
        return wrapper

    @property
    def dynamic(self):
        return to_python_reader(<DynamicValue.Reader>self.source, self.root)
    def __repr__(self):
        return repr(self.dynamic)

    {%- if c.union_fields != [] %}
    @property
    def which(self):
        return {{ c.cython_name }}_Which(self.source.which())
    @property
    def which_raw(self):
        return self.source.which()
    {%- endif %}

    {%- for field in c.fields %}

    @property
    def {{ field.cython_name }}(self):
        {%- if field.doc != "" %}
        """
        {{ field.doc | indent(8) }}
        """
        {%- endif %}
        {%- if field.sort == 'native' %}
        return self.source.get{{ field.cpp_name }}()
        {%- elif field.sort == 'struct' %}
        return {{ field.cython_return }}.init(self.source.get{{ field.cpp_name }}(), self.root)
        {%- elif field.sort == 'string' %}
        temp = self.source.get{{ field.cpp_name }}()
        return (<char*>temp.begin())[:temp.size()]
        {%- elif field.sort == 'enum' %}
        return {{ field.cython_return }}(self.source.get{{ field.cpp_name }}())
        {%- else %}
        error
        {%- endif %}
    {%- if field.union == True %}
    @property
    def is_{{ field.cython_name }}(self):
        return self.source.is{{ field.cpp_name }}()
    {%- endif %}
    {%- if field.gen_has == True %}
    @property
    def has_{{ field.cython_name }}(self):
        return self.source.has{{ field.cpp_name }}()
    {%- endif %}
    {%- endfor %}
{%- endfor %}


cdef class Uint16_List:

    @staticmethod
    cdef init(C_Uint16_List source, object root):
        cdef Uint16_List wrapper = Uint16_List.__new__(Uint16_List)
        wrapper.source = source
        wrapper.root = root
        return wrapper

    def __getitem__(self, uint index):
        source = self.source
        if index >= source.size():
            raise IndexError('Out of bounds')
        return source[index]

    def __len__(self):
        return self.source.size()

cdef class Uint32_List:

    @staticmethod
    cdef init(C_Uint32_List source, object root):
        cdef Uint32_List wrapper = Uint32_List.__new__(Uint32_List)
        wrapper.source = source
        wrapper.root = root
        return wrapper

    def __getitem__(self, uint index):
        source = self.source
        if index >= source.size():
            raise IndexError('Out of bounds')
        return source[index]

    def __len__(self):
        return self.source.size()

cdef class Uint64_List:

    @staticmethod
    cdef init(C_Uint64_List source, object root):
        cdef Uint64_List wrapper = Uint64_List.__new__(Uint64_List)
        wrapper.source = source
        wrapper.root = root
        return wrapper

    def __getitem__(self, uint index):
        source = self.source
        if index >= source.size():
            raise IndexError('Out of bounds')
        return source[index]

    def __len__(self):
        return self.source.size()

cdef class Int64_List:

    @staticmethod
    cdef init(C_Int64_List source, object root):
        cdef Int64_List wrapper = Int64_List.__new__(Int64_List)
        wrapper.source = source
        wrapper.root = root
        return wrapper

    def __getitem__(self, uint index):
        source = self.source
        if index >= source.size():
            raise IndexError('Out of bounds')
        return source[index]

    def __len__(self):
        return self.source.size()

cdef class String_List:

    @staticmethod
    cdef init(C_String_List source, object root):
        cdef String_List wrapper = String_List.__new__(String_List)
        wrapper.source = source
        wrapper.root = root
        return wrapper

    def __getitem__(self, uint index):
        source = self.source
        if index >= source.size():
            raise IndexError('Out of bounds')
        temp = source[index]
        return (<char*>temp.begin())[:temp.size()]

    def __len__(self):
        return self.source.size()

{%- for c in classes_lists %}
cdef class {{ c.cython_name }}_List:

    @staticmethod
    cdef init(C_{{ c.cython_name }}_List source, object root):
        cdef {{ c.cython_name }}_List wrapper = {{ c.cython_name }}_List.__new__({{ c.cython_name }}_List)
        wrapper.source = source
        wrapper.root = root
        return wrapper

    def __getitem__(self, uint index):
        source = self.source
        if index >= source.size():
            raise IndexError('Out of bounds')
        return {{ c.cython_name }}.init(source[index], self.root)

    def __len__(self):
        return self.source.size()
{%- endfor %}
