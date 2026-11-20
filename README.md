# Métodos Formais

> Projeto da disciplina **Métodos Formais** — Ciência da Computação, UDESC.

## Sobre

Repositório com listas de exercícios, provas e anotações de estudo da disciplina, escritos em **Coq** (Gallina). Os exercícios envolvem definir funções e tipos indutivos e provar propriedades sobre eles usando táticas como `intros`, `simpl`, `rewrite`, `induction`, `destruct` e `apply`.

## Conteúdo

### Listas de exercícios

| Lista | Tema | Principais definições e teoremas |
|-------|------|----------------------------------|
| 1 | Indução: números binários | tipo `bin`, `incr`, `bin_to_nat`, `nat_to_bin`, `normalize`; `bin_to_nat_pres_incr`, `nat_bin_nat`, `bin_nat_bin` |
| 2 | Mais sobre indução | `div2`, `sum`; `plus_n_Sm`, `mul2_div2`, `div2_mult2_plus`, `mult_Sn_m`, `sum_n` |
| 3 | Listas e polimorfismo | `fold`, `fold_length`, `fold_map`, `foldl`; `app_length`, `rev_app_distr`, `app_comm_fold`, `fold_map_correct` |
| 3 | Split e combine | `combine`, `split`; `combine_split`, `split_combine` |
| 5 | Lógica | `dist_not_exists`, `dist_exists_or`, `In_map_iff`, `In_app_iff`, `excluded_middle_irrefutable`, `Peirce_double_negation` |
| 6 | Operadores relacionais | relações `<=` e `le'`; `le_trans`, `le_plus_l`, `lt_ge_cases`, `le_le'`, `plus_lt` |
| 7 | Expressões regulares | `reg_exp`, `exp_match`, `reg_exp_of_list_spec`, `re_not_empty_correct`, `weak_pumping` (lema do bombeamento, versão fraca) |

### Provas e exames

- **Primeira prova (6/6/2022)** — `evenb_2`, `even_S_odd`, `combine_nil` e `involutive_f_map`.
- **Primeira prova (13/10/2025)** — `evenb_2`, `even_S_odd`, `rev_app_distr` e `involutive_f_map`.
- **Prova 2** — expressões regulares: `union_inv`, distributividade da concatenação sobre a união e elemento neutro da concatenação.
- **Exames** — `p_or_negp`, `even_S_odd`, `le'_n_Sm` e `le_le'`; `repeat_n`, `le_plus_l`, `repeat_index` e `index_map`; `or_distributes_over_and`, `min_correct` e a relação indutiva `myle`.

### Anotações de estudo

`Estudo-geral-COQ.v` reúne um roteiro de estudo: ambiente (CoqIDE, VsCoq, versão online), comandos básicos (`Inductive`, `Definition`, `Fixpoint`, `match`), um tipo indutivo `even` com provas de que 0, 2 e 4 são pares, um resumo das táticas essenciais e, por fim, as provas da comutatividade da adição (`comutatividade`, por indução em `n`) e de `forall n, n = n` (`n_igual_n`).

## Tecnologias

- Coq / Gallina (bibliotecas padrão `Lists.List`, `Arith`, `PeanoNat` e a tática `lia`)

## Estrutura

```
.
├── Estudo-geral-COQ.v                 # anotações de estudo
├── Lista1 - Indução.v                 # enunciado da lista 1, parcialmente resolvido
├── Lista2 - Mais sobre Indução.v      # enunciado da lista 2 (provas em aberto, com Admitted)
├── Lista3 - LIstas e Polimorfismo.v   # lista 3, com uma prova em aberto
├── Prova1.v                           # primeira prova (6/6/2022)
├── New folder/                        # cópia dos arquivos .v da raiz (com a versão antiga, incompleta, do Estudo-geral-COQ.v)
├── Listas MFO/                        # listas 1, 2, 3, 5, 6 e 7 resolvidas, salvas em .txt
└── Consulta MFO/
    ├── Listas/                        # as mesmas listas em .v (Exercicio1.v é o enunciado da lista 1)
    └── Provas/                        # provas e exames resolvidos, usados como material de consulta
```

## Como executar

Com o Coq instalado, cada arquivo `.v` pode ser verificado individualmente:

```bash
coqc Estudo-geral-COQ.v
coqc "Consulta MFO/Listas/ListaOpRel.v"
```

Também é possível abrir os arquivos no CoqIDE ou no VS Code (VsCoq) para acompanhar as provas passo a passo. Os arquivos de `Listas MFO/` estão em `.txt`; para verificá-los, copie o conteúdo para um arquivo `.v`.

## Autores

- Arthur Bertoli Silva

Os cabeçalhos de alguns arquivos de prova (`Prova1.v` e os arquivos em `Consulta MFO/Provas/`) trazem os nomes de outros estudantes, Herton Silveira e Igor Schiessl Froehner. Esses arquivos foram guardados como material de consulta.
