"""Private roster import: one uppercase pinyin initial per character."""
import re
from pypinyin import lazy_pinyin, Style

# Surname readings differ from the usual dictionary reading of these characters.
SURNAMES = {'曾':'Z','单':'S','解':'X','区':'O','仇':'Q','查':'Z','朴':'P','乐':'Y',
            '尉迟':'YC','万俟':'MQ'}

def name_initials(name):
    name = name.strip()
    prefix = next((s for s in sorted(SURNAMES, key=len, reverse=True) if name.startswith(s)), '')
    rest = name[len(prefix):]
    initials = SURNAMES.get(prefix, '') + ''.join(lazy_pinyin(rest, style=Style.FIRST_LETTER)).upper()
    initials = re.sub(r"[\s·•.'-]", '', initials)
    if not re.fullmatch(r'[A-Z]{1,80}', initials):
        raise ValueError('Name requires a manually reviewed initials value in the private roster.')
    return initials
