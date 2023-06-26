import React from "react";
import NavBar from "./NavBar";
import Footer from "./Footer";
import HomePage from "./HomePage";
import Report from "./Report";
import List from "./List";
import Search from "./Search";
import Map from "./Map";
import {dentistTheme, doctorTheme} from "./styles/theme";
import {ThemeProvider} from "@mui/material";
import {Route} from "wouter";

export default function Application({context}) {

    return (
        <>
            <ThemeProvider theme={context.projectName === "Doctor Watch" ? doctorTheme : dentistTheme}>
                <NavBar context={context}/>
                {/*<BrowserRouter>*/}
                {/*    <Routes>*/}
                {/*        <Route path=":context" element={<HomePageWrapper/>}/>*/}
                {/*        <Route path="/report" element={<Report/>}/>*/}
                {/*        <Route path="/map" element={<Map/>}/>*/}
                {/*        <Route path="/search" element={<Search/>}/>*/}
                {/*        <Route path="/list" element={<List/>}/>*/}
                {/*    </Routes>*/}
                {/*</BrowserRouter>*/}
                <Route path="/"><HomePage context={context}/></Route>
                <Route path="/report"><Report/></Route>
                <Route path="/map"><Map/></Route>
                <Route path="/search"><Search/></Route>
                <Route path="/list"><List/></Route>
                <Footer context={context}/>
            </ThemeProvider>
        </>
    )
}


