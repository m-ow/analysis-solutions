
import VersoBlog
import AnalysisBook.Home

open Verso Genre Blog Site Syntax

open Output Html Template Theme in
def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <head>
          <meta charset="UTF-8"/>
          <title>{{ (← param (α := String) "title") }} " — Verso "</title>
          <link rel="stylesheet" href="/static/style.css"/>
          <script>"window.__versoSiteRoot=\"/analysis/\""</script>
          {{← builtinHeader }}
        </head>
        <body>
          <header>
            <div class="inner-wrap">

            <nav class="top" role="navigation">
              <ol>
                <li><a href="/">"Home"</a></li>
                <li><a href="/docs/">"Documentation"</a></li>
                {{ ← dirLinks (← read).site }}
              </ol>
            </nav>
          </div>
          </header>
          <div class="main" role="main">
            <div class="wrap">
              {{ (← param "content") }}
            </div>
          </div>
        </body>
      </html>
    }}
  }
  |>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩


def_literate_page sec21 from Analysis.Section_2_1 in "../analysis" as "The Peano Axioms"

def_literate_page sec22 from Analysis.Section_2_2 in "../analysis" as "Addition"
def_literate_page sec23 from Analysis.Section_2_3 in "../analysis" as "Multiplication"
def_literate_page sec2e from Analysis.Section_2_epilogue in "../analysis" as "Equivalence of naturals"
def_literate_page sec31 from Analysis.Section_3_1 in "../analysis" as "Fundamentals"
def_literate_page sec41 from Analysis.Section_4_1 in "../analysis" as "The integers"
def_literate_page sec42 from Analysis.Section_4_2 in "../analysis" as "The rationals"
def_literate_page sec43 from Analysis.Section_4_3 in "../analysis" as "Absolute value and exponentiation"
def_literate_page sec51 from Analysis.Section_5_1 in "../analysis" as "Cauchy sequences"
def_literate_page sec52 from Analysis.Section_5_2 in "../analysis" as "Equivalent Cauchy sequences"
def_literate_page sec53 from Analysis.Section_5_3 in "../analysis" as "The construction of the real numbers"
def_literate_page sec54 from Analysis.Section_5_4 in "../analysis" as "Ordering the reals"

def demoSite : Site := site AnalysisBook.Home /
  static "static" ← "./static_files"
  "sec21" sec21
  "sec22" sec22
  "sec23" sec23
  "sec2e" sec2e
  "sec31" sec31
  "sec41" sec41
  "sec42" sec42
  "sec43" sec43
  "sec51" sec51
  "sec52" sec52
  "sec53" sec53
  "sec54" sec54

def baseUrl := "https://teorth.github.io/analysis/docs/"

def linkTargets : Code.LinkTargets where
  const name := .some <| s!"{baseUrl}find?pattern={name}#doc"
  definition name := .some <| s!"{baseUrl}find?pattern={name}#doc"

def main := blogMain theme demoSite (linkTargets := linkTargets)
