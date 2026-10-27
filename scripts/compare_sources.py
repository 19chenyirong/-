#!/usr/bin/env python3
"""Compare the five fixed straight-line C functions with OpenHarmony source."""
import re
from support import ROOT, CASES, FUNCTIONS, require
TOKEN_PATTERN = re.compile(r'->|[A-Za-z_][A-Za-z_0-9]*|[0-9]+|[=*(),;]')

def mask_comments(text):
    return re.sub(r'/\*.*?\*/|//[^\n]*',
                  lambda match: ''.join('\n' if character == '\n' else ' ' for character in match[0]),
                  text, flags=re.S)


def tokens(text):
    result = TOKEN_PATTERN.findall(text)
    require(''.join(result) == re.sub(r'\s+', '', text), f'Unsupported C syntax: {text!r}')
    return result


def extract_function(text, name):
    masked = mask_comments(text)
    pattern = (r'\b(?:static\s+inline\s+void|LITE_OS_SEC_ALW_INLINE\s+STATIC\s+INLINE\s+VOID)\s+'
               + re.escape(name) + r'\s*\(([^()]*)\)\s*\{')
    definitions = list(re.finditer(pattern, masked))
    require(len(definitions) == 1, f'Expected one definition of {name}, found {len(definitions)}')
    match = definitions[0]
    closing = masked.find('}', match.end())
    require(closing != -1, f'Unclosed function: {name}')
    body = masked[match.end():closing]
    require('{' not in body, f'Only the selected straight-line functions are supported: {name}')
    segments = body.split(';')
    require(not segments[-1].strip(), f'Unterminated statement: {name}')
    statements = []
    offset = match.end()
    for segment in segments[:-1]:
        require(bool(segment.strip()), f'Unexpected empty statement: {name}')
        start = offset + len(segment) - len(segment.lstrip())
        statement = ' '.join(segment.split()) + ';'
        statements.append(dict(line=masked.count('\n', 0, start) + 1, text=statement, tokens=tokens(statement)))
        offset += len(segment) + 1
    signature = ' '.join(masked[match.start():masked.find(')', match.start()) + 1].split())
    return dict(signature=signature, parameters=tokens(match[1]),
                start_line=masked.count('\n', 0, match.start()) + 1,
                end_line=masked.count('\n', 0, closing) + 1, statements=statements)


def extract_structure(text):
    masked = mask_comments(text)
    definitions = list(re.finditer(r'typedef\s+struct\s+LOS_DL_LIST\s*\{([^{}]*)\}\s*LOS_DL_LIST\s*;', masked))
    require(len(definitions) == 1, 'Expected one LOS_DL_LIST definition')
    match = definitions[0]
    fields = [tokens(segment) for segment in match[1].split(';') if segment.strip()]
    require(fields == [['struct', 'LOS_DL_LIST', '*', 'pstPrev'], ['struct', 'LOS_DL_LIST', '*', 'pstNext']],
            'LOS_DL_LIST fields or their declaration order changed')
    return dict(start_line=masked.count('\n', 0, match.start()) + 1,
                end_line=masked.count('\n', 0, match.end()) + 1, fields=fields)


def normalize_null(statement_tokens, function):
    result = list(statement_tokens)
    if function == 'LOS_ListDelete' and '=' in result:
        assignment = result.index('=')
        if result[assignment + 1:-1] in (['NULL'], ['(', 'LOS_DL_LIST', '*', ')', '0']):
            result = result[:assignment + 1] + ['NULL_POINTER', ';']
    return result


def compare_sources():
    header = (ROOT / 'references/openharmony/los_list.h').read_text(encoding='utf-8')
    upstream_structure = extract_structure(header)
    structures = []
    for case in CASES:
        source = f'src/QCP_examples/LiteOS/{case}.c'
        structure = extract_structure((ROOT / source).read_text(encoding='utf-8'))
        require(structure['fields'] == upstream_structure['fields'], '链表结构声明不同')
        structures.append(dict(source=source, qcp=structure, openharmony=upstream_structure))
    files = ('LOS_ListInit', 'List_Add', 'List_Add', 'List_Add', 'LOS_ListDelete')
    functions = []
    for function, case, count in zip(FUNCTIONS, files, (2, 4, 1, 1, 4)):
        source = f'src/QCP_examples/LiteOS/{case}.c'
        qcp = extract_function((ROOT / source).read_text(encoding='utf-8'), function)
        upstream = extract_function(header, function)
        require(qcp['parameters'] == upstream['parameters'], f'参数不同：{function}')
        require(len(qcp['statements']) == len(upstream['statements']) == count, f'语句数不同：{function}')
        statements = []
        for a, b in zip(qcp['statements'], upstream['statements']):
            equal = a['tokens'] == b['tokens']
            normalized = normalize_null(a['tokens'], function) == normalize_null(b['tokens'], function)
            require(normalized, f'有序语句不同：{function}:{a["line"]}')
            statements.append(dict(qcp=a, openharmony=b, raw_equal=equal, null_normalized_equal=normalized))
        functions.append(dict(function=function, source=source, qcp=qcp, openharmony=upstream,
                              statements=statements, parameters_equal=True))
    statements = [s for f in functions for s in f['statements']]
    return dict(structures=structures, functions=functions, statement_count=len(statements),
                raw_equal_count=sum(s['raw_equal'] for s in statements),
                null_spelling_difference_count=sum(not s['raw_equal'] for s in statements),
                scope='固定源码的结构、参数和顺序语句对照；不表示全部编译配置下的形式化等价。')
