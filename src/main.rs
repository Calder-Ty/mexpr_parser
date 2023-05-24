//! Parse some of that sweet, sweet text
use mexpr_parser::{LetExpression, ParseError};

const QUERY_DEF: &str = r##"let
    Source = Odbc.Query("dsn=Starburst", "SELECT#(lf)id,#(lf)dag_id,#(lf)state,#(lf)external_trigger,#(lf)start_date,#(lf)run_type#(lf)#(lf)FROM #(")airflow_postgres#(").public.dag_run"),
    #"Replaced Value" = Table.ReplaceValue(Source,"UTC","",Replacer.ReplaceText,{"start_date"}),
    #"Changed Type" = Table.TransformColumnTypes(#"Replaced Value",{{"start_date", type datetime}}),
    #"Changed Type1" = Table.TransformColumnTypes(#"Changed Type",{{"start_date", type date}})
in
    #"Changed Type1"
"##;

fn main() -> Result<(), Box<ParseError>> {
    let (_, res) = LetExpression::try_parse(QUERY_DEF)?;
    dbg!(res);
    Ok(())
}
