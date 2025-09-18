#!/usr/bin/env python3

import os
import sys
import keyword
from typing import Any
from jinja2 import Environment, PackageLoader
import inflection

import capnp
import capnp.schema_capnp as schema_capnp

def cython_name(name):
    return '_'.join([inflection.camelize(p) for p in name.split(':')[1].split('.')])

def cpp_name(name):
    return '::'.join([inflection.camelize(p) for p in name.split(':')[1].split('.')])

def pycapnp_name(name):
    return '.'.join([inflection.camelize(p) for p in name.split(':')[1].split('.')])

def mk_return(cpp, cython, sort):
    return {'cpp_return': cpp, 'cython_return': cython, 'sort': sort}

def gen_list_type_info(nodes, list_type):
    list_which = list_type.elementType.which()
    if list_which in ['void', 'bool',
                        'int8', 'int16', 'int32', 'int64',
                        'uint8', 'uint16', 'uint32', 'uint64',
                        'float32', 'float64']:
        return list_which.capitalize(), None
    elif list_which == 'text':
        return 'String', None
    elif list_which == 'data':
        return 'String', None
    elif list_which == 'list':
        return None # TODO
    elif list_which == 'enum':
        return None # TODO
    elif list_which == 'struct':
        return (
            cython_name(nodes[list_type.elementType.struct.typeId].displayName)+'_Reader',
            cpp_name(nodes[list_type.elementType.struct.typeId].displayName)
        )
    elif list_which == 'interface':
        return None
    elif list_which == 'anyPointer':
        return None # TODO
    else: assert False

def gen_type_info(nodes, type, list_accum):
    which = type.which()
    if which == 'void':
        return mk_return('void', None, 'native')
    elif which == 'bool':
        return mk_return('cbool', None, 'native')
    elif which in ['int8', 'int16', 'int32', 'int64',
                    'uint8', 'uint16', 'uint32', 'uint64']:
        return mk_return(which+'_t', None, 'native')
    elif which == 'float32':
        return mk_return('float', None, 'native')
    elif which == 'float64':
        return mk_return('double', None, 'native')
    elif which == 'text':
        return mk_return('StringPtr', None, 'string')
    elif which == 'data':
        return mk_return('StringPtr', None, 'string')
    elif which == 'list':
        sub_type = gen_list_type_info(nodes, type.list)
        if sub_type is None:
            return None
        cython_type, cpp_type = sub_type
        if cpp_type is not None:
            list_accum.add((cython_type, cpp_type))
        return mk_return('C_'+cython_type+'_List', cython_type+'_List', 'struct')
    elif which == 'enum':
        name = nodes[type.enum.typeId].displayName
        return mk_return(cython_name(name), None, 'enum')
    elif which == 'struct':
        name = nodes[type.struct.typeId].displayName
        return mk_return('C_'+cython_name(name)+'_Reader', cython_name(name)+'_Reader', 'struct')
    elif which == 'interface':
        return None # TODO
    elif which == 'anyPointer':
        return None # TODO
    else: assert False

def main():
    env = Environment(loader=PackageLoader('generate_api'))

    code = schema_capnp.CodeGeneratorRequest.read(sys.stdin)
    nodes = {node.id: node for node in code.nodes}
    sourceInfo = {node.id: node for node in code.sourceInfo}
    classes = []
    classes_lists = set()
    enums = []
    for node in code.nodes:
        if node.scopeId == 0:
            continue # These are RPC argument structs, which we skip for now
        if node.which() == 'struct':
            struct = node.struct
            c_info = {'cython_name': cython_name(node.displayName),
                      'cpp_name': cpp_name(node.displayName),
                      'pycapnp_name': pycapnp_name(node.displayName),
                      'fields': [],
                      'union_fields': []}
            for field_index, field in enumerate(struct.fields):
                if field.which() == 'slot':
                    f_info: dict[str, Any]
                    if info := gen_type_info(nodes, field.slot.type, classes_lists):
                        f_info = info
                    else:
                        continue
                elif field.which() == 'group':
                    name = nodes[field.group.typeId].displayName
                    f_info = mk_return('C_'+cython_name(name)+'_Reader', cython_name(name)+'_Reader', 'struct')
                else: assert False
                f_info['cpp_name'] = inflection.camelize(field.name)
                cn = inflection.underscore(field.name)
                if cn in keyword.kwlist:
                    cn += '_'
                f_info['cython_name'] = cn
                if schema_capnp.Field.noDiscriminant != field.discriminantValue:
                    f_info['union'] = True
                    c_info['union_fields'].append(inflection.underscore(field.name).upper())
                else:
                    f_info['union'] = False
                f_info['gen_has'] = (field.which() == 'slot' and field.slot.type.which() in
                                     ['text', 'data', 'list', 'struct', 'interface', 'anyPointer'])
                f_info['doc'] = sourceInfo[node.id].members[field_index].docComment.strip()
                c_info['fields'].append(f_info)
            c_info['is_group'] = struct.isGroup
            c_info['doc'] = sourceInfo[node.id].docComment.strip()
            classes.append(c_info)
        elif node.which() == 'enum':
            e_info = {'cython_name': cython_name(node.displayName),
                      'cpp_name': 'capnp::schemas::'+cpp_name(node.displayName)+'_'+f'{node.id:x}',
                      'pycapnp_name': pycapnp_name(node.displayName),
                      'enumerants': [inflection.underscore(e.name).upper() for e in node.enum.enumerants]}
            enums.append(e_info)

    pyx = env.get_template("capnp_cython.pyx")
    pxd = env.get_template("capnp_cython.pxd")
    classes_lists = [{'cython_name': cython_name, 'cpp_name': cpp_name} for cython_name, cpp_name in classes_lists]
    filename = os.path.join(os.path.dirname(__file__), 'graph_api_capnp_cython')
    with open(filename+'.pyx', "w") as out:
        out.write(pyx.render(classes=classes, classes_lists=classes_lists, enums=enums))
    with open(filename+'.pxd', "w") as out:
        out.write(pxd.render(classes=classes, classes_lists=classes_lists, enums=enums))

if __name__ == '__main__':
    main()
