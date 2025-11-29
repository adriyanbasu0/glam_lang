use super::token::Token;

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Let(LetStatement),
    Return(ReturnStatement),
    Expression(ExpressionStatement),
    Print(PrintStatement), // Added PrintStatement
    Struct(StructDefinition),
}

#[derive(Debug, PartialEq, Clone)]
pub struct StructDefinition {
    pub name: Identifier,
    pub fields: Vec<StructField>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct StructField {
    pub name: Identifier,
    pub field_type: Identifier, // For now, types are just identifiers
}

#[derive(Debug, PartialEq, Clone)]
pub struct PrintStatement {
    pub expression: Expression,
}

#[derive(Debug, PartialEq, Clone)]
pub struct LetStatement {
    pub name: Identifier,
    pub value: Expression,
}

#[derive(Debug, PartialEq, Clone)]
pub struct ReturnStatement {
    pub return_value: Expression,
}

#[derive(Debug, PartialEq, Clone)]
pub struct ExpressionStatement {
    pub expression: Expression,
}

#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    Identifier(Identifier),
    IntLiteral(IntLiteral),
    StringLiteral(StringLiteral),
    Boolean(Boolean),
    Prefix(PrefixExpression),
    Infix(InfixExpression),
    If(IfExpression),
    Function(FunctionLiteral),
    Call(CallExpression),
    Access(AccessExpression),
    StructInstance(StructInstanceExpression),
    Null,
}

#[derive(Debug, PartialEq, Clone)]
pub struct AccessExpression {
    pub object: Box<Expression>,
    pub field: Identifier,
}

#[derive(Debug, PartialEq, Clone)]
pub struct StructInstanceExpression {
    pub struct_name: Identifier,
    pub fields: Vec<(Identifier, Expression)>, // (field_name, field_value)
}

#[derive(Debug, PartialEq, Clone)]
pub struct Identifier {
    pub value: String,
}

#[derive(Debug, PartialEq, Clone)]
pub struct IntLiteral {
    pub value: i64,
}

#[derive(Debug, PartialEq, Clone)]
pub struct StringLiteral {
    pub value: String,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Boolean {
    pub value: bool,
}

#[derive(Debug, PartialEq, Clone)]
pub struct PrefixExpression {
    pub operator: Token,
    pub right: Box<Expression>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct InfixExpression {
    pub left: Box<Expression>,
    pub operator: Token,
    pub right: Box<Expression>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct IfExpression {
    pub condition: Box<Expression>,
    pub consequence: BlockStatement,
    pub alternative: Option<BlockStatement>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct FunctionLiteral {
    pub parameters: Vec<Identifier>,
    pub body: BlockStatement,
}

#[derive(Debug, PartialEq, Clone)]
pub struct CallExpression {
    pub function: Box<Expression>, // Identifier or FunctionLiteral
    pub arguments: Vec<Expression>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct BlockStatement {
    pub statements: Vec<Statement>,
}

#[derive(Debug, PartialEq, Clone)]
pub struct Program {
    pub statements: Vec<Statement>,
}
