//! Parse some of that sweet, sweet text
use std::{eprintln, println};

use mexpr_parser::LetExpression;

const QUERY_DEF: &str = r##"let
    Source = Odbc.Query("dsn=Starburst", "SELECT#(lf)id,#(lf)dag_id,#(lf)state,#(lf)external_trigger,#(lf)start_date,#(lf)run_type#(lf)#(lf)FROM #(")airflow_postgres#(").public.dag_run"),
    #"Replaced Value" = Table.ReplaceValue(Source,"UTC","",Replacer.ReplaceText,{"start_date"}),
    #"Changed Type" = Table.TransformColumnTypes(#"Replaced Value",{{"start_date", type datetime}}),
    #"Changed Type1" = Table.TransformColumnTypes(#"Changed Type",{{"start_date", type date}})
in
    #"Changed Type1"
"##;

fn main() {
    let res = LetExpression::try_parse(QUERY_DEF);
    match res {
        Ok((_, v)) => println!("{:#?}", v),
        Err(e) => eprintln!("{}", e)
    };
}
