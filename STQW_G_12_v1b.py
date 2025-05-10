import tkinter as tk
from tkinter import messagebox

# Определяем узлы синтаксического дерева
class Node:
    def eval(self, values):
        raise NotImplementedError
    def to_string(self):
        raise NotImplementedError

class VarNode(Node):
    def __init__(self, name):
        self.name = name
    def eval(self, values):
        return values[self.name]
    def to_string(self):
        return self.name

class NotNode(Node):
    def __init__(self, child):
        self.child = child
    def eval(self, values):
        return not self.child.eval(values)
    def to_string(self):
        s = self.child.to_string()
        if isinstance(self.child, OpNode):
            return "~(" + s + ")"
        else:
            return "~" + s

class OpNode(Node):
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right
    def eval(self, values):
        a = self.left.eval(values)
        b = self.right.eval(values)
        if self.op == '∧':
            return a and b
        if self.op == '∨':
            return a or b
        if self.op == '⊕':
            return (a != b)
        if self.op == '↓' or self.op == '⊽':  # NOR
            return not (a or b)
        if self.op == '↑':  # NAND
            return not (a and b)
        if self.op == '→':
            return (not a) or b
        if self.op == '↔':
            return a == b
        raise ValueError(f"Неизвестный оператор {self.op}")
    def to_string(self):
        prec = {'~': 8, '∧':7, '∨':6, '⊕':5, '↓':4, '⊽':4, '↑':3, '→':2, '↔':1}
        left_str = self.left.to_string()
        right_str = self.right.to_string()
        # Скобки для левого операнда
        if isinstance(self.left, OpNode) and prec[self.left.op] < prec[self.op]:
            left_str = "(" + left_str + ")"
        # Скобки для правого операнда (особый случай импликации)
        if isinstance(self.right, OpNode):
            if self.op == '→' or prec[self.right.op] <= prec[self.op]:
                right_str = "(" + right_str + ")"
        return left_str + self.op + right_str

# Лексер: разбивает ввод на токены (переменные и символы операторов)
def tokenize(expr):
    tokens = []
    i = 0
    while i < len(expr):
        ch = expr[i]
        if ch.isspace():
            i += 1; continue
        if ch.isalnum():
            j = i
            while j < len(expr) and expr[j].isalnum():
                j += 1
            tokens.append(expr[i:j])
            i = j
        else:
            tokens.append(ch)
            i += 1
    return tokens

# Парсер: алгоритм сортировочной станции преобразует токены в AST
op_prec = {'~': 8, '∧':7, '∨':6, '⊕':5, '↓':4, '⊽':4, '↑':3, '→':2, '↔':1}
left_assoc = {'∧':True, '∨':True, '⊕':True, '↓':True, '⊽':True, '↑':True, '→':True, '↔':True}

def parse_expression(tokens):
    output = []
    stack = []
    for tok in tokens:
        if tok.isalnum():
            output.append(VarNode(tok))
        elif tok == '~':
            stack.append(tok)
        elif tok == '(':
            stack.append(tok)
        elif tok == ')':
            while stack and stack[-1] != '(':
                op = stack.pop()
                if op == '~':
                    node = NotNode(output.pop()); output.append(node)
                else:
                    right = output.pop(); left = output.pop()
                    output.append(OpNode(op, left, right))
            if not stack or stack[-1] != '(':
                raise ValueError("Неверные скобки")
            stack.pop()
        else:
            # Оператор
            while stack:
                top = stack[-1]
                if top == '(':
                    break
                if top in op_prec and ((op_prec[top] > op_prec[tok]) or
                   (op_prec[top] == op_prec[tok] and left_assoc.get(tok, True))):
                    op = stack.pop()
                    if op == '~':
                        node = NotNode(output.pop()); output.append(node)
                    else:
                        right = output.pop(); left = output.pop()
                        output.append(OpNode(op, left, right))
                    continue
                break
            stack.append(tok)
    while stack:
        op = stack.pop()
        if op in ('(', ')'):
            raise ValueError("Неверные скобки")
        if op == '~':
            node = NotNode(output.pop()); output.append(node)
        else:
            right = output.pop(); left = output.pop()
            output.append(OpNode(op, left, right))
    if len(output) != 1:
        raise ValueError("Некорректное выражение")
    return output[0]

# Собирает промежуточные подвыражения (в порядке вычисления)
def collect_subexpressions(node, seen=None, subs=None):
    if subs is None:
        subs = []
    if seen is None:
        seen = set()
    if isinstance(node, OpNode):
        collect_subexpressions(node.left, seen, subs)
        collect_subexpressions(node.right, seen, subs)
        expr_str = node.to_string()
        if expr_str not in seen:
            subs.append((expr_str, node))
            seen.add(expr_str)
    elif isinstance(node, NotNode):
        collect_subexpressions(node.child, seen, subs)
        expr_str = node.to_string()
        if expr_str not in seen:
            subs.append((expr_str, node))
            seen.add(expr_str)
    return subs

# Строим таблицу истинности
def generate_truth_table(expr):
    tokens = tokenize(expr)
    if not tokens:
        raise ValueError("Пустое выражение")
    tree = parse_expression(tokens)
    vars = sorted({tok for tok in tokens if tok.isalnum()})
    if not vars:
        raise ValueError("Нет переменных")
    subexprs = collect_subexpressions(tree)
    rows = []
    n = len(vars)
    for bits in range(2**n):
        assignment = {}
        for i, var in enumerate(vars):
            # Переменная с индексом 0 соответствует старшему биту
            assignment[var] = bool((bits >> (n-1-i)) & 1)
        row = [int(assignment[var]) for var in vars]
        for expr_str, node in subexprs:
            row.append(int(node.eval(assignment)))
        # Итоговое значение всего выражения
        row.append(int(tree.eval(assignment)))
        rows.append(row)
    headers = vars + [expr_str for expr_str,_ in subexprs] + ["результат"]
    return headers, rows

# Обработчик кнопки: выводит таблицу или сообщение об ошибке
def show_truth_table():
    expr = entry.get().strip()
    try:
        headers, rows = generate_truth_table(expr)
    except Exception as e:
        messagebox.showerror("Ошибка", str(e))
        return
    text.configure(state='normal')
    text.delete("1.0", tk.END)
    # Вычисляем ширину каждого столбца
    widths = [len(h) for h in headers]
    for row in rows:
        for i, val in enumerate(row):
            widths[i] = max(widths[i], len(str(val)))
    fmt = "".join("{:<" + str(w+2) + "}" for w in widths) + "\n"
    # Печатаем заголовки и строки
    text.insert(tk.END, fmt.format(*headers))
    for row in rows:
        text.insert(tk.END, fmt.format(*[str(v) for v in row]))
    text.configure(state='disabled')

##
def insert_symbol(symbol):
    entry.insert(entry.index(tk.INSERT), symbol)
##



# Настройка GUI
root = tk.Tk()
root.title("Калькулятор логических функций")
root.configure(bg='#B0C4DE') ## цвет фона
root.geometry('777x555+900+450')
tk.Label(root,bg='#8FBC8F', text="Введите логическое выражение:").pack(padx=5, pady=5) # цвет надписи
entry = tk.Entry(root, width=60, bg='#EEE8AA') # цвет поля ввода
entry.pack(padx=5, pady=5)
##
  # Кнопки для вставки логических операторов
button_frame = tk.Frame(root,bg='#AFEEEE') ## цвет под кнопками
button_frame.pack(pady=5)

symbols = ['~', '∧', '∨', '⊕', '↓', '⊽', '↑', '→', '↔']
for sym in symbols:
    btn = tk.Button(button_frame, bg='#AFEEEE', text=sym, width=3, command=lambda s=sym: insert_symbol(s))##+цвет кнопок
    btn.pack(side=tk.LEFT, padx=2)
##
tk.Button(root, bg='#8FBC8F',  text="Построить таблицу истинности", command=show_truth_table).pack(padx=5, pady=5)# цвет кнопки вывода таблицы
text = tk.Text(root, bg='#EEE8AA', height=25, width=80, font=("Courier", 10)) # цвет поля вывода таблицы истинности
text.pack(padx=5, pady=5)
root.mainloop()
