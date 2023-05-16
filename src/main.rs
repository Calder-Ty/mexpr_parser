//! Parse some of that sweet, sweet text
use mexpr_parser::Parser;

const QUERY_DEF: &str = r##"let
    Source = Odbc.Query("dsn=Starburst", "SELECT#(lf)id,#(lf)dag_id,#(lf)state,#(lf)external_trigger,#(lf)start_date,#(lf)run_type#(lf)#(lf)FROM #(")airflow_postgres#(").public.dag_run"),
    #"Replaced Value" = Table.ReplaceValue(Source,"UTC","",Replacer.ReplaceText,{"start_date"}),
    #"Changed Type" = Table.TransformColumnTypes(#"Replaced Value",{{"start_date", type datetime}}),
    #"Changed Type1" = Table.TransformColumnTypes(#"Changed Type",{{"start_date", type date}})
in
    #"Changed Type1"
"##;

fn main() {
    let mut parser = Parser::default();
    parser.parse(QUERY_DEF);
}
