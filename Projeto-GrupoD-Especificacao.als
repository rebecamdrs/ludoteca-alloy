sig Partida {
	jogo: one Jogo,
	mesa: one Mesa,
	horario: one Horario,
	participantes: set Jogador,
	organizador: one Jogador
}

sig Jogo {
	categoria: one Categoria
}

abstract sig Categoria {}
one sig Estrategia extends Categoria {}
one sig Party extends Categoria {}
one sig Cooperativo extends Categoria {}

sig Jogador {}

sig Mesa {}

sig Horario {}