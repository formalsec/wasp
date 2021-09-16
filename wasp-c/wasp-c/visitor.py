from pycparser import (
    c_parser,
    c_ast,
    c_generator 
)

cnt = 0

class MethodNotImplemented(Exception):
    """Exception raised when visit method not available"""

    def __init__(self, name):
        self.name = name
        self.message = f'visit_{name}: method not implemented'
        super().__init__(self.message)

class MyVisitor(c_ast.NodeVisitor):

    def _safe_visit(self, node):
        return self.visit(node) if node is not None else node

    def _safe_map(self, f, lst):
        return map(f, lst) if lst is not None else lst

    def _get_binop_func(self, op):
        if op == '&&':
            return '__logand'
        elif op == '||':
            return '__logor'
        else:
            raise RuntimeError

    def visit_ArrayDecl(self, node):
        return node
    
    def visit_ArrayRef(self, node):
        return node

    def visit_Assignment(self, node):
        return c_ast.Assignment(
            node.op,
            self.visit(node.lvalue),
            self.visit(node.rvalue),
            node.coord
        )

    def visit_BinaryOp(self, node):
        if node.op in ['&&', '||']:
            return c_ast.FuncCall(
                c_ast.ID(self._get_binop_func(node.op)),
                c_ast.ExprList([
                    self.visit(node.left),
                    self.visit(node.right)
                ]),
                node.coord
            )
        return c_ast.BinaryOp(
            node.op,
            self.visit(node.left),
            self.visit(node.right),
            node.coord
        )

    def visit_Break(self, node):
        return node

    def visit_Case(self, node):
        return c_ast.Case(
            self.visit(node.expr),
            map(self.visit, node.stmts),
            node.coord
        )

    def visit_Cast(self, node):
        return c_ast.Cast(
            node.to_type,
            self.visit(node.expr),
            node.coord
        )

    def visit_Compound(self, node):
        return c_ast.Compound(
            self._safe_map(self.visit, node.block_items),
            node.coord
        )

    def visit_CompoundLiteral(self, node):
        return c_ast.CompoundLiteral(
            node.type,
            self.visit(node.init),
        )

    def visit_Constant(self, node):
        return node

    def visit_Continue(self, node):
        return node

    def visit_Decl(self, node):
        return node

    def visit_DeclList(self, node):
        return c_ast.DeclList(
            map(self.visit, node.decls),
            node.coord
        )

    def visit_Default(self, node):
        return c_ast.Default(
            map(self.visit, node.stmts),
            node.coord
        )

    def visit_DoWhile(self, node):
        return c_ast.DoWhile(
            self.visit(node.cond),
            self.visit(node.stmt),
            node.coord
        )

    def visit_EllipsisParam(self, node):
        return node
       
    def visit_EmptyStatement(self, node):
        return node

    def visit_Enum(self, node):
        return node

    def visit_Enumerator(self, node):
        return node

    def visit_EnumeratorList(self, node):
        return node

    def visit_ExprList(self, node):
        return c_ast.ExprList(
            map(self.visit, node.exprs),
            node.coord
        )

    def visit_FileAST(self, node):
        print(node.show())
        return c_ast.FileAST(
            map(self.visit, node.ext), 
            node.coord
        )

    def visit_For(self, node):
        return c_ast.For(
            self.visit(node.init),
            self.visit(node.cond),
            self.visit(node.next),
            self.visit(node.stmt),
            node.coord
        )

    def visit_FuncCall(self, node):
        return c_ast.FuncCall(
            node.name,
            self._safe_visit(node.args),
            node.coord
        )

    def visit_FuncDecl(self, node):
        return node

    def visit_FuncDef(self, node):
        return c_ast.FuncDef(
            node.decl,
            node.param_decls,
            self.visit(node.body),
            node.coord
        )

    def visit_Goto(self, node):
        return node

    def visit_ID(self, node):
        return node

    def visit_IdentifierType(self, node):
        return node
    
    def visit_If(self, node):
        global cnt
        cnt = cnt + 1
        n_cond = c_ast.FuncCall(
            c_ast.ID('IFG'),
            c_ast.ExprList([
                self.visit(node.cond), 
                c_ast.Constant('int', str(cnt))
            ]),
            node.coord
        )
        return c_ast.If(
            n_cond,
            self.visit(node.iftrue),
            self._safe_visit(node.iffalse),
            node.coord
        )

    def visit_InitList(self, node):
        return c_ast.InitList(
            map(self.visit, node.exprs),
            node.coord
        )

    def visit_Label(self, node):
        return c_ast.Label(
            node.name,
            self.visit(node.stmt),
            node.coord,
        )

    def visit_NamedInitializer(self, node):
        return c_ast.NamedInitializer(
            map(self.visit, node.name),
            self.visit(node.expr),
            node.coord
        )

    def visit_ParamList(self, node):
        return c_ast.ParamList(
            map(self.visit, node.params),
            node.coord
        )

    def visit_PtrDecl(self, node):
        return node

    def visit_Return(self, node):
        return c_ast.Return(
            self._safe_visit(node.expr),
            node.coord
        )

    def visit_Struct(self, node):
        return node

    def visit_StructRef(self, node):
        return node

    def visit_Switch(self, node):
        return c_ast.Switch(
            self.visit(node.cond),
            self.visit(node.stmt),
            node.coord
        )

    def visit_TernaryOp(self, node):
        return c_ast.FuncCall(
            c_ast.ID('__ternary'),
            c_ast.ExprList([
                self.visit(node.cond),
                self.visit(node.iftrue),
                self.visit(node.iffalse)
            ]),
            node.coord
        )

    def visit_TypeDecl(self, node):
        return node

    def visit_Typedef(self, node):
        return node

    def visit_Typename(self, node):
        return node
    
    def visit_UnaryOp(self, node):
        return c_ast.UnaryOp(
            node.op,
            self.visit(node.expr),
            node.coord
        )
        
    def visit_Union(self, node):
        return node

    def visit_While(self, node):
        return c_ast.While(
            self.visit(node.cond),
            self.visit(node.stmt),
            node.coord
        )

    def visit_Pragma(self, node):
        return node

    def generic_visit(self, node):
        raise MethodNotImplemented(node.__class__.__name__)
