# Sistema de Partidas em uma Ludoteca de Jogos de Tabuleiro

```Projeto para Lógica para Computação [2026.1]```

## Sobre o projeto

Este repositório contém a especificação em Alloy do tema **"Sistema de Partidas em uma Ludoteca de Jogos de Tabuleiro"**, modelando as regras que controlam como partidas de jogos de tabuleiro são organizadas: jogos, mesas, horários, jogadores e as restrições que evitam conflitos de agenda e monopolização de mesas.

### Regras de negócio modeladas

- Todo jogo pertence a exatamente uma categoria: `Estrategia`, `Party` ou `Cooperativo`.
- Toda partida está associada a exatamente um jogo, uma mesa e um horário.
- Cada partida tem entre 2 e 6 participantes, incluindo um organizador que obrigatoriamente é um dos participantes.
- Um jogador não pode estar em duas partidas no mesmo horário (nem como organizador, nem como participante comum).
- Uma mesma mesa não pode sediar duas partidas no mesmo horário.
- Nenhum jogador pode organizar mais de duas partidas ao todo.
- Mesas e jogos podem existir sem nenhuma partida vinculada (acervo cadastrado antes de qualquer evento).

## Estrutura do repositório

```
ludoteca-alloy/
├── README.md
├── Projeto-GrupoY-Especificacao.als
└── testes/
    └── cenarios-experimentais.als
```

## Como rodar

1. Baixe o Alloy Analyzer (versão 6.2.0) em [alloytools.org/download.html](https://alloytools.org/download.html). Requer Java instalado.
2. Execute o `.jar`, ou no Windows use `alloy.exe` direto.
3. Abra o arquivo `.als` pelo menu **File > Open**.
4. Para verificar uma asserção, clique com o botão direito na linha `check ...` e escolha **Execute**. O resultado esperado é **"No counterexample found"**.
5. Para gerar o cenário de exemplo, execute a linha `run cenarioExemplo`. Uma instância será exibida no Visualizer.

## Referências

- [Alloy Tutorial oficial](https://alloytools.org/tutorials/online/)
- [Documentação do Alloy](https://alloytools.org/)