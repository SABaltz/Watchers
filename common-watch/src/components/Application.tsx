import React from "react";
import {BrowserRouter, Route, Routes} from "react-router-dom";
import NavBar from "./NavBar";
import Footer from "./Footer";
import HomePage from "./HomePage";
import Report from "./Report";
import List from "./List";
import Search from "./Search";
import Map from "./Map";
import {dentistTheme, doctorTheme} from "./styles/theme";
import {ThemeProvider} from "@mui/material";

export default function Application({context}) {

    return (
        <>
            <ThemeProvider theme={context.projectName === "Doctor Watch" ? doctorTheme : dentistTheme}>
                <NavBar context={context}/>
                <BrowserRouter>
                    <Routes>
                        <Route path="/" element={<HomePage context={context}/>}/>
                        <Route path="/report" element={<Report/>}/>
                        <Route path="/map" element={<Map/>}/>
                        <Route path="/search" element={<Search/>}/>
                        <Route path="/list" element={<List/>}/>
                    </Routes>
                </BrowserRouter>
                <Footer context={context}/>
            </ThemeProvider>
        </>
    )
}
