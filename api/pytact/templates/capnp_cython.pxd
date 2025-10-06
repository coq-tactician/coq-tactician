from capnp.includes.types cimport *
from capnp cimport helpers
from capnp.includes.capnp_cpp cimport DynamicValue, StringPtr
from capnp.lib.capnp cimport _DynamicStructReader, to_python_reader, reraise_kj_exception

cdef extern from "capnp/schema-parser.h" namespace " ::capnp":
    cdef cppclass C_SchemaParser"capnp::SchemaParser" nogil:
        {%- for c in classes %}
        void loadCompiledTypeAndDependencies{{ c.cython_name }}"loadCompiledTypeAndDependencies<{{ c.cpp_name }}>"()
        {%- endfor %}

cdef extern from "graph_api.capnp.h":

    {%- for c in classes %}

    cdef cppclass C_{{ c.cython_name }}_Reader "{{ c.cpp_name }}::Reader":
        {%- if c.fields == [] %}
        pass
        {%- endif %}
        {%- if c.union_fields != [] %}
        {{ c.cython_name }}_Which which() except +reraise_kj_exception
        {%- endif %}
        {%- for field in c.fields %}
        {{ field.cpp_return }} get{{ field.cpp_name }}() except +reraise_kj_exception
        {%- if field.union== True %}
        cbool is{{ field.cpp_name }}() except +reraise_kj_exception
        {%- endif %}
        {%- if field.gen_has == True %}
        cbool has{{ field.cpp_name }}() except +reraise_kj_exception
        {%- endif %}
        {%- endfor %}

    {%- if c.union_fields != [] %}
    cpdef enum class {{ c.cython_name }}_Which "{{ c.cpp_name }}::Which"(uint16_t):
        {%- for field in c.union_fields %}
        {{ field }},
        {%- endfor %}
    {%- endif %}
    {%- endfor %}

    {%- for e in enums %}
    cpdef enum class {{ e.cython_name }} "{{ e.cpp_name }}"(uint16_t):
        {%- for enumerant in e.enumerants %}
        {{ enumerant }},
        {%- endfor %}
    {%- endfor %}

    cdef cppclass C_DynamicStruct_Reader" ::capnp::DynamicStruct::Reader":
        {%- for c in classes %}
        C_{{ c.cython_name }}_Reader as{{ c.cython_name }}"as<{{ c.cpp_name }}>"()
        {%- endfor %}

cdef extern from "capnp/list.h":
    cdef cppclass C_Uint16_List " ::capnp::List<uint16_t, ::capnp::Kind::PRIMITIVE>::Reader":
        uint16_t operator[](uint) except +reraise_kj_exception
        uint size()
    cdef cppclass C_Uint32_List " ::capnp::List<uint32_t, ::capnp::Kind::PRIMITIVE>::Reader":
        uint32_t operator[](uint) except +reraise_kj_exception
        uint size()
    cdef cppclass C_Uint64_List " ::capnp::List<uint64_t, ::capnp::Kind::PRIMITIVE>::Reader":
        uint64_t operator[](uint) except +reraise_kj_exception
        uint size()
    cdef cppclass C_Int64_List " ::capnp::List<int64_t, ::capnp::Kind::PRIMITIVE>::Reader":
        int64_t operator[](uint) except +reraise_kj_exception
        uint size()
    cdef cppclass C_String_List " ::capnp::List<capnp::Text, ::capnp::Kind::BLOB>::Reader":
        StringPtr operator[](uint) except +reraise_kj_exception
        uint size()

    {%- for c in classes_lists %}
    cdef cppclass C_{{ c.cython_name }}_List " ::capnp::List<{{ c.cpp_name }}, ::capnp::Kind::STRUCT>::Reader":
        C_{{ c.cython_name }} operator[](uint) except +reraise_kj_exception
        uint size()
    {%- endfor %}

{%- for c in classes %}

cdef class {{ c.cython_name }}_Reader:
    cdef C_{{ c.cython_name }}_Reader source
    cdef object root
    @staticmethod
    cdef init(C_{{ c.cython_name }}_Reader source, object root)
{%- endfor %}

cdef class Uint16_List:
    cdef C_Uint16_List source
    cdef object root
    @staticmethod
    cdef init(C_Uint16_List source, object root)

cdef class Uint32_List:
    cdef C_Uint32_List source
    cdef object root
    @staticmethod
    cdef init(C_Uint32_List source, object root)

cdef class Uint64_List:
    cdef C_Uint64_List source
    cdef object root
    @staticmethod
    cdef init(C_Uint64_List source, object root)

cdef class Int64_List:
    cdef C_Int64_List source
    cdef object root
    @staticmethod
    cdef init(C_Int64_List source, object root)

cdef class String_List:
    cdef C_String_List source
    cdef object root
    @staticmethod
    cdef init(C_String_List source, object root)

{%- for c in classes_lists %}
cdef class {{ c.cython_name }}_List:
    cdef C_{{ c.cython_name }}_List source
    cdef object root
    @staticmethod
    cdef init(C_{{ c.cython_name }}_List source, object root)
{%- endfor %}
